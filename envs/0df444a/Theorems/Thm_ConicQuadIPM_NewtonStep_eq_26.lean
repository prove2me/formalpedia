-- Prove2me | Theorems.Thm_ConicQuadIPM_NewtonStep_eq_26
-- name    : ConicQuadIPM.NewtonStep.eq_26
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:02.773338+00:00
-- url     : https://prove2.me/theorems/5f6abe3d-225b-4a92-bd76-db8729b423bb
-- title:
--   (26), proof of Lemma 4.1, p. 13 — 0 = (ηx⁽⁰⁾ + d_x)ᵀ(ηs⁽⁰⁾ + d_s) + (ητ⁽⁰⁾ + d_τ)(ηκ⁽⁰⁾ + d_κ) and its expansion
-- statement:
--   In the setting of the Newton system (22) of Andersen, Roos and Terlaky — a product cone $K = K^1\times\cdots\times K^k$ with the usual dimension conventions, data $A$, $b$, $c$, any point $(x^{(0)},\tau^{(0)},y^{(0)},s^{(0)},\kappa^{(0)})$, $\gamma\in[0,1]$ and a solution $(d_x,d_\tau,d_y,d_s,d_\kappa)$ of (22) — put $\eta = 1-\gamma$. Then
--   $$
--   \begin{aligned}
--   0 &= (\eta x^{(0)} + d_x)^T(\eta s^{(0)} + d_s) + (\eta\tau^{(0)} + d_\tau)(\eta\kappa^{(0)} + d_\kappa)\\
--   &= \eta^2\big((x^{(0)})^Ts^{(0)} + \tau^{(0)}\kappa^{(0)}\big) + \eta\big((x^{(0)})^Td_s + (s^{(0)})^Td_x + \tau^{(0)}d_\kappa + \kappa^{(0)}d_\tau\big) + d_x^Td_s + d_\tau d_\kappa.
--   \end{aligned}
--   $$
--
--   The first equality says that the shifted direction of (25) is complementary; the second expands the product. Together with the value of the middle term computed on p. 14 it yields the orthogonality $d_x^Td_s + d_\tau d_\kappa = 0$.
--
--   **Formalization Note** Both equalities of (26) are stated, as a conjunction: the first equality, and the expansion of its right-hand side. $x^Ts$ is $\sum_i (x^i)^Ts^i$ over the blocks; $\eta$ is written out as $1-\gamma$. The hypothesis $\gamma\in[0,1]$ is the range of (21) and is not needed.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 13, proof of Lemma 4.1, (26)

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting

namespace ConicQuadIPM.NewtonStep

open Matrix

theorem eq_26
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    0 = (∑ i, ((1 - γ) • x0 i + dx i) ⬝ᵥ ((1 - γ) • s0 i + ds i))
          + ((1 - γ) * τ0 + dτ) * ((1 - γ) * κ0 + dκ) ∧
    (∑ i, ((1 - γ) • x0 i + dx i) ⬝ᵥ ((1 - γ) • s0 i + ds i))
          + ((1 - γ) * τ0 + dτ) * ((1 - γ) * κ0 + dκ)
      = (1 - γ) ^ 2 * ((∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0)
        + (1 - γ) * ((∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i) + τ0 * dκ + κ0 * dτ)
        + ((∑ i, dx i ⬝ᵥ ds i) + dτ * dκ) := by sorry

end ConicQuadIPM.NewtonStep
