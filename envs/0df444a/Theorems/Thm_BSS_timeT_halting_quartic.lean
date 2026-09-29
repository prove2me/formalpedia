-- Prove2me | Theorems.Thm_BSS_timeT_halting_quartic
-- name    : BSS.timeT_halting_quartic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T15:04:53.834136+00:00
-- url     : https://prove2.me/theorems/06336093-d242-445d-a40b-736b0352ce73
-- title:
--   §4 Theorem: the time-$T$ halting set is a projected quartic zero set
-- statement:
--   The Theorem of §4 (p. 20). Let $M$ be a machine over $\mathbb{R}$ and $T$ a time bound, and let
--   $I_T = \{y : T_M(y) \le T\}$ be the time-$T$ halting set. Then there is a polynomial $f_T$ of
--   degree at most $4$, in the first $K_T$ input coordinates and finitely many auxiliary variables
--   $z$, with
--   $$y \in I_T \iff \exists z,\; f_T(y_1, \dots, y_{K_T}, z) = 0.$$
--
--   The polynomial is presented in the powerfree encoding of §5, so the milestone also fixes the
--   representation in which the reduction of §6 will deliver its output. The paper's additional
--   assertion — that the number of auxiliary variables and of monomials is bounded by a polynomial in
--   $T$ depending only on $M$ — is the quantitative half of the theorem and is not part of this
--   statement; it is what the hardness milestone must supply.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §4, p. 20, Theorem

import Definitions.Def_BSSFeasibility

namespace BSS

theorem timeT_halting_quartic (M : Machine ℝ) (T : ℕ) :
    ∃ (K : ℕ) (w : Rinf ℝ), IsPowerfreeCode w ∧
      ∀ y : Rinf ℝ,
        (∃ t ≤ T, M.HaltsBy y t) ↔
          ∃ x : ℕ → ℝ, (∀ i : ℕ, 1 ≤ i → i ≤ K → x i = y (i - 1)) ∧ feasValue w x = 0 := by sorry

end BSS
