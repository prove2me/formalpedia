-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_equality_case
-- name    : ConicQuadIPM.Complementarity.equality_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:36.436345+00:00
-- url     : https://prove2.me/theorems/b7e8a172-c1fc-4e14-abf9-6ebd8b3f81e4
-- title:
--   Appendix, p. 37 — xᵀs = 0 and (Tⁱxⁱ)₁, (Tⁱsⁱ)₁ ≠ 0 give (xⁱ)ᵀQⁱxⁱ = (sⁱ)ᵀQⁱsⁱ = 0 and (Tⁱxⁱ)₁(Tⁱsⁱ)₁ = ‖(Tⁱxⁱ)₂:ₙ‖‖(Tⁱsⁱ)₂:ₙ‖
-- statement:
--   Let $K=K^1\times\dots\times K^k$ be as in §3, let $x,s\in K$ be complementary, $x^Ts=0$, and let $i$ be a block with $(T^ix^i)_1\ne 0$ and $(T^is^i)_1\ne 0$. Then
--   $$
--   (x^i)^TQ^ix^i=0,\qquad (s^i)^TQ^is^i=0,\qquad
--   (T^ix^i)_1(T^is^i)_1=\|(T^ix^i)_{2:n}\|\,\|(T^is^i)_{2:n}\| .
--   $$
--
--   This is the equality case of the inequality chain: both points lie on the boundary of their cone, and Cauchy–Schwarz is tight.
--
--   **Formalization Note.** The two non-vanishing hypotheses are the page's case assumption ("Therefore, assume this is not the case"); without them the first two conclusions fail (e.g. $x^i=0$, $s^i$ interior). For a block of type $\mathbb R_+$ the hypotheses cannot hold together with $x^Ts=0$, as on the page. Euclidean norms are written out; block dimensions (`WellFormed`) are a disclosed hypothesis.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, Appendix, proof of Lemma 3.1, p. 37, first paragraph

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem equality_case {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x s : (i : Fin k) → Fin (n i) → ℝ)
    (hx : inK kind x) (hs : inK kind s) (hcomp : ∑ i, x i ⬝ᵥ s i = 0) (i : Fin k)
    (hx1 : coord (Tmat (kind i) (n i) *ᵥ x i) 0 ≠ 0)
    (hs1 : coord (Tmat (kind i) (n i) *ᵥ s i) 0 ≠ 0) :
    x i ⬝ᵥ (Qmat (kind i) (n i) *ᵥ x i) = 0 ∧
    s i ⬝ᵥ (Qmat (kind i) (n i) *ᵥ s i) = 0 ∧
    coord (Tmat (kind i) (n i) *ᵥ x i) 0 * coord (Tmat (kind i) (n i) *ᵥ s i) 0 =
      Real.sqrt (tailSq (Tmat (kind i) (n i) *ᵥ x i) 1) *
        Real.sqrt (tailSq (Tmat (kind i) (n i) *ᵥ s i) 1) := by sorry

end ConicQuadIPM.Complementarity
