-- Prove2me | Theorems.Thm_FWIterates_lemma_3_3
-- name    : FWIterates.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:25.989368+00:00
-- url     : https://prove2.me/theorems/5e683fe4-0a6c-4bf7-ad99-913552215e5b
-- title:
--   Lemma 3.3 — exact line search through a vertex orthogonal to its prescribed direction lands on that vertex
-- statement:
--   Let $f$, $(\eta_\ell)$ be given by Theorem 3.1 for sketch data $(\mathcal P_\ell,V_k,u_k,\delta_\ell)$, an open convex $\mathcal D\supset\mathcal P_0$ and $d\ge2$. Let $\mathcal C\subset\mathcal D$ be a compact convex set, $x_t,v_t\in\mathcal C$, and let
--   $$
--   \gamma_t\in\operatorname*{arg\,min}_{\gamma\in[0,1]}f(x_t+\gamma(v_t-x_t)),\qquad x_{t+1}=(1-\gamma_t)x_t+\gamma_tv_t .
--   $$
--   If there is $k$ such that $V_k\in[x_t,v_t]$ and $\langle v_t-x_t,u_k\rangle=0$, then $x_{t+1}=V_k$.
--
--   This is the mechanism of Counterexample 3.5: once the gradient direction prescribed at a vertex is orthogonal to the Frank-Wolfe direction through it, the exact line search stops exactly there.
--
--   **Formalization Note** The hypotheses "f and all other variables defined in Theorem 3.1" are the corrected hypotheses `IsSketch` together with the conclusions `IsInterpolant`.
--
--   Differences from the source:
--
--   - generalization: x_t an iterate and v_t ∈ arg min_{v∈C} ⟨v, ∇f(x_t)⟩ of a line-search Frank-Wolfe run on C → x, v any points of C and γ any line-search minimizer; reason: the conclusion holds for every such pair; it specializes to the run
--   - encoding: "the function f and all other variables defined in Theorem 3.1" → hypotheses IsSketch P V u δ (corrected) and IsInterpolant D d P V u δ f η, with D open convex, P 0 ⊆ D, d ≥ 2; reason: the data and conclusions of Theorem 3.1
--   - encoding: f : D → ℝ → f : ℝ² → ℝ with every property (convexity, smoothness, sublevel sets, gradient, Hessian) required on D only; reason: the values of f outside D never enter; D is open, so gradients and Hessians at points of D are the true ones
-- source:
--   Bolte, Combettes & Pauwels, The Iterates of the Frank-Wolfe Algorithm May Not Converge, arXiv:2202.08711v1, Lemma 3.3, p.5

import Mathlib
import Definitions.Def_FWIterates_IsSketch
import Definitions.Def_FWIterates_IsInterpolant

open scoped RealInnerProductSpace

namespace FWIterates

/-- **Lemma 3.3** (arXiv:2202.08711v1, Lemma 3.3, p.5). Let `f`, `η` be as produced by
Theorem 3.1 for sketch data `P, V, u, δ`, an open convex `D ⊇ P 0` and `d ≥ 2`. Let `C ⊆ D` be
compact convex, and consider one Frank-Wolfe step with the line-search rule (iii) from `xₜ ∈ C`
towards `vₜ ∈ C`. If some `V k` lies on the segment `[xₜ, vₜ]` and `⟨vₜ − xₜ, u k⟩ = 0`, then
every line-search step lands on it: `xₜ₊₁ = (1 − γₜ)xₜ + γₜvₜ = V k` for every
`γₜ ∈ argmin_{γ ∈ [0,1]} f(xₜ + γ(vₜ − xₜ))`.

**Formalization Note** `vₜ` is any point of `C`; whether it is an oracle output plays no role
(the lemma holds a fortiori for oracle outputs). The data "defined in Theorem 3.1" are its
(corrected) hypotheses `IsSketch` together with its conclusions `IsInterpolant`. -/
theorem lemma_3_3 (P : ℕ → Set (EuclideanSpace ℝ (Fin 2)))
    (V u : ℕ → EuclideanSpace ℝ (Fin 2)) (δ : ℕ → ℝ) (hS : IsSketch P V u δ)
    (D : Set (EuclideanSpace ℝ (Fin 2))) (hD : IsOpen D) (hDc : Convex ℝ D) (hPD : P 0 ⊆ D)
    (d : ℕ) (hd : 2 ≤ d) (f : EuclideanSpace ℝ (Fin 2) → ℝ) (η : ℕ → ℝ)
    (hI : IsInterpolant D d P V u δ f η)
    (C : Set (EuclideanSpace ℝ (Fin 2))) (hCD : C ⊆ D) (hC : IsCompact C) (hCc : Convex ℝ C)
    (x v : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ C) (hv : v ∈ C) (k : ℕ)
    (hVk : V k ∈ segment ℝ x v) (horth : ⟪v - x, u k⟫ = 0)
    (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hls : ∀ γ' ∈ Set.Icc (0 : ℝ) 1, f (x + γ • (v - x)) ≤ f (x + γ' • (v - x))) :
    (1 - γ) • x + γ • v = V k := by sorry

end FWIterates
