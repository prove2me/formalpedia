-- Prove2me | Theorems.Thm_BBBV_RandomPermutation_theorem_3_1
-- name    : BBBV.RandomPermutation.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:32.981858+00:00
-- url     : https://prove2.me/theorems/102e0406-5ef8-47dc-ae5f-adbccf86cfe6
-- title:
--   Theorem 3.1 — Euclidean distance bounds the distance of observed distributions
-- statement:
--   Let $u$ and $v$ be unit vectors in a finite-dimensional complex Hilbert space with a fixed orthonormal computational basis. If $\|u-v\|\le\varepsilon$, then the distributions obtained by observing their basis coordinates satisfy
--
--   $$\sum_c\bigl||u_c|^2-|v_c|^2\bigr|\le 4\varepsilon.$$
--
--   This converts a bound on final quantum states into a bound on measurement outcomes.
--
--   **Formalization Note** Total variation follows the paper's footnote 7: the sum of absolute differences, with no factor $1/2$.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 7, Theorem 3.1 and footnote 7

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_QueryModel

namespace BBBV.RandomPermutation

theorem theorem_3_1 {ι : Type} [Fintype ι] (u v : EuclideanSpace ℂ ι)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ε : ℝ) (h : ‖u - v‖ ≤ ε) :
    (∑ c : ι, |‖u c‖ ^ 2 - ‖v c‖ ^ 2|) ≤ 4 * ε := by sorry

end BBBV.RandomPermutation
