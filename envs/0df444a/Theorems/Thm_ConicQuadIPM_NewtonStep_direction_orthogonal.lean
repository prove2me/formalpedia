-- Prove2me | Theorems.Thm_ConicQuadIPM_NewtonStep_direction_orthogonal
-- name    : ConicQuadIPM.NewtonStep.direction_orthogonal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:53.221987+00:00
-- url     : https://prove2.me/theorems/41f68530-d67b-41e7-91c6-de11ff7c8822
-- title:
--   Proof of Lemma 4.1, p. 14 — the Newton direction is orthogonal: d_xᵀd_s + d_τd_κ = 0
-- statement:
--   In the setting of the Newton system (22) — a product cone $K = K^1\times\cdots\times K^k$ with the usual dimension conventions, data $A$, $b$, $c$, any point $(x^{(0)},\tau^{(0)},y^{(0)},s^{(0)},\kappa^{(0)})$, $\gamma\in[0,1]$ and a solution $(d_x,d_\tau,d_y,d_s,d_\kappa)$ of (22) — the primal and dual parts of the direction are orthogonal:
--   $$
--   d_x^Td_s + d_\tau d_\kappa = 0.
--   $$
--
--   Orthogonality is what makes the complementarity gap along the step $z^{(0)} + \alpha d$ linear in $\alpha$, with no quadratic term; it is the fourth identity of Lemma 4.1.
--
--   **Formalization Note** $d_x^Td_s = \sum_i (d_x^i)^Td_s^i$ over the blocks. The hypothesis $\gamma\in[0,1]$ is the range of (21) and is not needed. No interiority of the current point is assumed, as in Lemma 4.1.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 14, proof of Lemma 4.1, 'These two facts combined gives d_xᵀd_s + d_τd_κ = 0'

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting

namespace ConicQuadIPM.NewtonStep

open Matrix

theorem direction_orthogonal
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    (∑ i, dx i ⬝ᵥ ds i) + dτ * dκ = 0 := by sorry

end ConicQuadIPM.NewtonStep
