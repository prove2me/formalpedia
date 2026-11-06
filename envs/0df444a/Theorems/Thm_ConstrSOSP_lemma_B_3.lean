-- Prove2me | Theorems.Thm_ConstrSOSP_lemma_B_3
-- name    : ConstrSOSP.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:41.663405+00:00
-- url     : https://prove2.me/theorems/b95aa8e9-f36b-41a1-882b-aee4f8bb0fa8
-- title:
--   Lemma B.3: transfer between interior and constrained stationarity
-- statement:
--   Let $\mathcal X=\{Ax\le b\}\subseteq\mathbb R^d$ be full-dimensional, $0<\rho\le1$, $x\in\mathcal X_\rho$, and let $g$, $H$ be the gradient and Hessian values at $x$. All precisions are positive.
--
--   **Theorem.**
--
--   1. If $x$ is an $(\eta_G,\eta_H)$-SOSP2, then $\|g\|\le\eta_G/\rho$ and $H\succeq-(\eta_H/\rho^2)I$; thus $x$ is an $(\eta_G/\rho,\eta_H/\rho^2)$-SOSP and an $(\eta_G/\rho,\eta_H/\rho^2)$-SOSP1 (for every $L_1>0$).
--   2. If $x$ is an $(\alpha_G,\alpha_H)$-SOSP1 with $\alpha_G<L_1\rho$, then it is an $(\alpha_G,\alpha_H)$-SOSP.
--   3. Every $(\alpha_G,\alpha_H)$-SOSP is an $(\alpha_G,\alpha_H)$-SOSP1 (for every $L_1>0$) and an $(\alpha_G,\alpha_H)$-SOSP2.
--
--   Away from the boundary the three stationarity notions agree up to constant changes of accuracy; this transfers the hardness of Interior-Sosp to Sosp1 and Sosp2.
--
--   Differences from the source:
--   - generalization: g(x) = ∇f(x), H(x) = ∇²f(x) for an objective f → arbitrary vectors g and matrices H at x; reason: the lemma uses f only through these values; it specializes to g = ∇f(x), H = ∇²f(x)
--   - generalization: rational 0 < ρ ≤ 1 → real 0 < ρ ≤ 1; reason: the proof does not use rationality; specializes to rational ρ
--   - encoding: X_ρ = {x ∈ X : dist(x, ∂X) ≥ ρ} → x ∈ X and the open Euclidean ball of radius ρ around x lies in X; reason: equivalent for a closed convex X; avoids Mathlib's sup-norm distance
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Lemma B.3, p.85

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ConstrSOSP_Poly
import Definitions.Def_ConstrSOSP_XRho
import Definitions.Def_ConstrSOSP_IsSOSP
import Definitions.Def_ConstrSOSP_IsSOSP1
import Definitions.Def_ConstrSOSP_IsSOSP2

namespace ConstrSOSP

/-- **Lemma B.3** (arXiv:2604.02285, 2 Nov 2026, p.85): "Assume X is full dimensional, and write
g(x) = ∇f(x) and H(x) = ∇²f(x). Fix rational 0 < ρ ≤ 1, and let X_ρ = {x ∈ X : dist(x, ∂X) ≥ ρ}.
Lemma B.3 (Transfer between interior and constrained stationarity). Let x ∈ X_ρ. (i) If x is an
(ηG, ηH)-SOSP2, then ‖g(x)‖ ≤ ηG/ρ, H(x) ⪰ −(ηH/ρ²)I. Thus it is an (ηG/ρ, ηH/ρ²)-SOSP, and hence
also an (ηG/ρ, ηH/ρ²)-SOSP1. (ii) If x is an (αG, αH)-SOSP1 with αG < L1ρ, then it is an
(αG, αH)-SOSP. Conversely, every (αG, αH)-SOSP is an (αG, αH)-SOSP1 and an (αG, αH)-SOSP2."

For a full-dimensional polytope `X = {Ax ≤ b} ⊆ ℝᵈ`, `0 < ρ ≤ 1`, `x ∈ X_ρ`, and gradient and
Hessian values `g`, `H` at `x`, with positive precisions:
1. an `(ηG, ηH)`-SOSP2 satisfies `‖g‖ ≤ ηG/ρ` and `vᵀHv ≥ −ηH/ρ²` for unit `v`, is an
   `(ηG/ρ, ηH/ρ²)`-SOSP, and is an `(ηG/ρ, ηH/ρ²)`-SOSP1 for every `L₁ > 0`;
2. an `(αG, αH)`-SOSP1 (proximal constant `L₁ > 0`) with `αG < L₁ρ` is an `(αG, αH)`-SOSP;
3. an `(αG, αH)`-SOSP is an `(αG, αH)`-SOSP1 (every `L₁ > 0`) and an `(αG, αH)`-SOSP2.

**Formalization Note** `X_ρ` is `XRho` (open Euclidean ball of radius `ρ` inside `X`). The
statement is for arbitrary data `g`, `H` at `x`, not only the derivatives of an objective. -/
theorem lemma_B_3 {m d : ℕ} (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (hfull : (interior (Poly A b)).Nonempty) (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1)
    (x g : Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (hx : x ∈ XRho A b ρ) :
    (∀ ηG ηH : ℝ, 0 < ηG → 0 < ηH → IsSOSP2 A b ηG ηH x g H →
      (ApproxVI.euclNorm g ≤ ηG / ρ ∧ ∀ v : Fin d → ℝ, ApproxVI.euclNorm v = 1 → -(ηH / ρ ^ 2) ≤ v ⬝ᵥ Matrix.mulVec H v) ∧
      IsSOSP A b (ηG / ρ) (ηH / ρ ^ 2) x g H ∧
      ∀ L1 : ℝ, 0 < L1 → IsSOSP1 A b L1 (ηG / ρ) (ηH / ρ ^ 2) x g H) ∧
    (∀ L1 αG αH : ℝ, 0 < L1 → 0 < αG → 0 < αH → αG < L1 * ρ →
      IsSOSP1 A b L1 αG αH x g H → IsSOSP A b αG αH x g H) ∧
    (∀ L1 αG αH : ℝ, 0 < L1 → 0 < αG → 0 < αH → IsSOSP A b αG αH x g H →
      IsSOSP1 A b L1 αG αH x g H ∧ IsSOSP2 A b αG αH x g H) := by sorry

end ConstrSOSP
