-- Prove2me | Theorems.Thm_Devaney_exists_continuous_period_five_not_three
-- name    : Devaney.exists_continuous_period_five_not_three
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:47:47.926858+00:00
-- url     : https://prove2.me/theorems/c5a65319-a50e-4d13-ae9c-bd6d66d13331
-- title:
--   Converse of Sarkovskii's theorem — a map with period five but no period three
-- statement:
--   There is a continuous map of the real line with a periodic point of prime period five and no periodic point of prime period three.
--
--   This is the sharpness half of Sarkovskii's theorem: the ordering cannot be improved. Devaney's witness is the piecewise-linear map of $[1,5]$ determined by $1 \mapsto 3 \mapsto 4 \mapsto 2 \mapsto 5 \mapsto 1$, for which a direct check of the images of $f^3$ on the four subintervals shows that the only fixed point of $f^{3}$ is the fixed point of $f$.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, pp. 66–67, the example following Remark 3

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem exists_continuous_period_five_not_three :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, HasPrimePeriod f x 5) ∧ ¬ ∃ x, HasPrimePeriod f x 3 := by sorry
end Devaney
