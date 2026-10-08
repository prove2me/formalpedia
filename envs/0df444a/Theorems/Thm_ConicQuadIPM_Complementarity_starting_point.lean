-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_starting_point
-- name    : ConicQuadIPM.Complementarity.starting_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:29.917984+00:00
-- url     : https://prove2.me/theorems/efd73c25-dd8c-48ec-905f-4b08078279df
-- title:
--   §6.1, pp. 28–29 — the starting point xⁱ⁽⁰⁾ = sⁱ⁽⁰⁾ = Tⁱe₁ⁱ, τ⁽⁰⁾ = κ⁽⁰⁾ = 1 lies in N(1)
-- statement:
--   Let $K=K^1\times\dots\times K^k$ be as in §3 and define the starting point
--   $$
--   x^{i(0)}=s^{i(0)}=T^ie^i_1\quad(i=1,\dots,k),\qquad \tau^{(0)}=\kappa^{(0)}=1,
--   $$
--   where $e^i_1$ is the first unit vector of $\mathbb R^{n^i}$. Then
--   $$
--   (x^{(0)},\tau^{(0)},s^{(0)},\kappa^{(0)})\in\mathcal N(1).
--   $$
--
--   The algorithm of the paper starts from this point, so it starts on the central path.
--
--   **Formalization Note.** The page also sets $y^{(0)}=0$, which plays no role in $\mathcal N(\beta)$ and is omitted. Block dimensions (`WellFormed`) are a disclosed hypothesis.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, §6.1, pp. 28–29

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem starting_point {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) :
    Nbhd kind n 1
      (fun i => Tmat (kind i) (n i) *ᵥ (e1 : Fin (n i) → ℝ)) 1
      (fun i => Tmat (kind i) (n i) *ᵥ (e1 : Fin (n i) → ℝ)) 1 := by sorry

end ConicQuadIPM.Complementarity
