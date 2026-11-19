-- Prove2me | Theorems.Thm_ArithmeticKakeya_arithmetic_kakeya_1675
-- name    : ArithmeticKakeya.arithmetic_kakeya_1675
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T22:01:15.524182+00:00
-- url     : https://prove2.me/theorems/243d25d0-0eef-4209-9f61-b8f3cd3bbe17
-- title:
--   Arithmetic Kakeya: a constructible proof of score $\le 1.675$
-- statement:
--   Exhibit a finite dilate set $X\subset\mathbb Z^2$ containing $(0,0)$ whose non-zero elements have non-zero coordinate sum, an $X$-constructible graph $G$, and a forcing $X$-set $(R,T)$ with $|T|<n(G)$ and score $(m(G)+|R|)/(n(G)-|T|)\le 1.675=67/40$ (stated in cross-multiplied form). This is the FrontierMath open problem at its default difficulty: any such object improves the best known arithmetic Kakeya exponent $\vartheta=1.6751308\dots$ and hence the known Kakeya dimension lower bounds in high dimensions.
-- source:
--   https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya (Problem section, default difficulty 1.675)

import Mathlib
import Definitions.Def_ArithmeticKakeya_grid
import Definitions.Def_ArithmeticKakeya_forcing

namespace ArithmeticKakeya
theorem arithmetic_kakeya_1675 :
    ∃ (X : Finset (ℤ × ℤ)) (G : ConstructibleGraph X)
      (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ)),
      (0, 0) ∈ X ∧
      (∀ x ∈ X, x ≠ (0, 0) → x.1 + x.2 ≠ 0) ∧
      IsXSet G R T ∧ Forces G R T ∧ T.length < n G ∧
      40 * (m G + R.length) ≤ 67 * (n G - T.length) := by sorry
end ArithmeticKakeya
