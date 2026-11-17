-- Prove2me | Theorems.Thm_ArithmeticKakeya_katz_tao_ak_theta
-- name    : ArithmeticKakeya.katz_tao_ak_theta
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T21:58:52.974208+00:00
-- url     : https://prove2.me/theorems/b347ac35-0f71-41ad-9bac-7a602a53855e
-- title:
--   Katz–Tao state of the art $\mathrm{AK}(\vartheta)$
-- statement:
--   Katz–Tao's current best bound: $\mathrm{AK}(\vartheta)$ holds, where $\vartheta=1.6751308\dots$ is the largest root of $x^3-4x+2=0$ (characterized as a root that is $\ge$ every root). It has stood since 2002.
-- source:
--   Katz–Tao, J. Anal. Math. 87 (2002); as stated in https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya

import Mathlib
import Definitions.Def_ArithmeticKakeya_ak

namespace ArithmeticKakeya
theorem katz_tao_ak_theta :
    ∃ ϑ : ℝ, ϑ ^ 3 - 4 * ϑ + 2 = 0 ∧
      (∀ x : ℝ, x ^ 3 - 4 * x + 2 = 0 → x ≤ ϑ) ∧ AK ϑ := by sorry
end ArithmeticKakeya
