-- Prove2me | Theorems.Thm_ArithmeticKakeya_lemm_sums_differences_barrier
-- name    : ArithmeticKakeya.lemm_sums_differences_barrier
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T21:59:40.751555+00:00
-- url     : https://prove2.me/theorems/856a5bea-e840-417b-9fe3-b36e6c9ab1bb
-- title:
--   Lemm's sums–differences barrier $>1.77898$
-- statement:
--   Lemm's lower bound: every forcing constructible proof for the sums–differences set $X=\{(1,0),(0,1),(1,1)\}$ has score strictly greater than $1.77898=88949/50000$. Equivalently the sums–differences exponent exceeds $1.77898$, so this method cannot reach the conjectured value. Stated in cross-multiplied form.
-- source:
--   Lemm, PAMS 143 (2015), Thm 2.1; as stated in https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya

import Mathlib
import Definitions.Def_ArithmeticKakeya_grid
import Definitions.Def_ArithmeticKakeya_forcing

namespace ArithmeticKakeya
theorem lemm_sums_differences_barrier
    (G : ConstructibleGraph ({(1, 0), (0, 1), (1, 1)} : Finset (ℤ × ℤ)))
    (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ))
    (hXT : IsXSet G R T) (hF : Forces G R T) (ht : T.length < n G) :
    88949 * (n G - T.length) < 50000 * (m G + R.length) := by sorry
end ArithmeticKakeya
