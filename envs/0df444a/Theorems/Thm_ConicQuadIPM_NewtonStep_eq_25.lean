-- Prove2me | Theorems.Thm_ConicQuadIPM_NewtonStep_eq_25
-- name    : ConicQuadIPM.NewtonStep.eq_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:36.244652+00:00
-- url     : https://prove2.me/theorems/4941840e-f1ce-4e60-b2aa-2a4f7a850eba
-- title:
--   (25), proof of Lemma 4.1, p. 13 — the shifted direction ηz⁽⁰⁾ + d solves the homogeneous equations, η = 1 − γ
-- statement:
--   Let $K = K^1\times\cdots\times K^k$ be a product of cones of the kinds $\mathbb R_+$, $K^q$, $K^r$ with the usual dimension conventions, let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, let $(x^{(0)},\tau^{(0)},y^{(0)},s^{(0)},\kappa^{(0)})$ be any point, $\gamma\in[0,1]$, and let $(d_x,d_\tau,d_y,d_s,d_\kappa)$ solve the Newton system (22). Put $\eta = 1-\gamma$. Then
--   $$
--   \begin{aligned}
--   A(\eta x^{(0)} + d_x) - b(\eta\tau^{(0)} + d_\tau) &= 0,\\
--   A^T(\eta y^{(0)} + d_y) + (\eta s^{(0)} + d_s) - c(\eta\tau^{(0)} + d_\tau) &= 0,\\
--   -c^T(\eta x^{(0)} + d_x) + b^T(\eta y^{(0)} + d_y) - (\eta\kappa^{(0)} + d_\kappa) &= 0.
--   \end{aligned}
--   $$
--
--   In words: the point $\eta(x^{(0)},\tau^{(0)},y^{(0)},s^{(0)},\kappa^{(0)}) + (d_x,d_\tau,d_y,d_s,d_\kappa)$ satisfies the linear equations of the homogeneous model. This is the first step of the proof of Lemma 4.1, and it is what makes the skew-symmetry argument (26) applicable.
--
--   **Formalization Note** The page prints $-c(\eta x^{(0)}+d_x)$ in the third line; the formal statement uses $-c^T(\eta x^{(0)}+d_x)$. The second identity is stated block by block. $\eta$ is written out as $1-\gamma$. The hypothesis $\gamma\in[0,1]$ is the range of (21) and is not needed for the identity.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 13, proof of Lemma 4.1, (25)

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting

namespace ConicQuadIPM.NewtonStep

open Matrix

theorem eq_25
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    (∑ i, A i *ᵥ ((1 - γ) • x0 i + dx i)) - ((1 - γ) * τ0 + dτ) • b = 0 ∧
    (∀ i, (A i)ᵀ *ᵥ ((1 - γ) • y0 + dy) + ((1 - γ) • s0 i + ds i)
        - ((1 - γ) * τ0 + dτ) • c i = 0) ∧
    -(∑ i, c i ⬝ᵥ ((1 - γ) • x0 i + dx i)) + b ⬝ᵥ ((1 - γ) • y0 + dy)
        - ((1 - γ) * κ0 + dκ) = 0 := by sorry

end ConicQuadIPM.NewtonStep
