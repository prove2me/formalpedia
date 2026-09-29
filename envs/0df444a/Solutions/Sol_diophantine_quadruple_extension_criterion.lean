-- Prove2me | solution 1 for diophantine_quadruple_extension_criterion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T19:58:36.492279+00:00
-- url     : https://prove2.me/submissions/2ad0dcea-9068-491b-b529-a2f51f76b57d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_diophantine_quadruple_extension_small_ratio
import Theorems.Thm_diophantine_quadruple_extension_medium_ratio
import Theorems.Thm_diophantine_quadruple_extension_large_ratio
import Definitions.Def_diophantine_descent

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open DiophantineDescent

theorem _root_.solution (a b c d : Nat)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hab2 : ∃ r : Nat, a * b + 1 = r ^ 2)
    (hac2 : ∃ s : Nat, a * c + 1 = s ^ 2)
    (hbc2 : ∃ t : Nat, b * c + 1 = t ^ 2)
    (had2 : ∃ u : Nat, a * d + 1 = u ^ 2)
    (hbd2 : ∃ v : Nat, b * d + 1 = v ^ 2)
    (hcd2 : ∃ w : Nat, c * d + 1 = w ^ 2)
    (r s t : Nat) (hr : a * b + 1 = r ^ 2)
    (hs : a * c + 1 = s ^ 2) (ht : b * c + 1 = t ^ 2)
    (hthresh : (b < 2 * a ∧ 9864 * b ^ 4 ≤ 1000 * c) ∨
      (2 * a ≤ b ∧ b ≤ 12 * a ∧ 4321 * b ^ 4 ≤ 1000 * c) ∨
      (12 * a < b ∧ 721800 * b ^ 4 ≤ 1000 * c)) :
    d = a + b + c + 2 * a * b * c + 2 * r * s * t := by
  rcases hthresh with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact diophantine_quadruple_extension_small_ratio a b c d ha hab hbc hcd
      hab2 hac2 hbc2 had2 hbd2 hcd2 r s t hr hs ht h1 h2
  · exact diophantine_quadruple_extension_medium_ratio a b c d ha hab hbc hcd
      hab2 hac2 hbc2 had2 hbd2 hcd2 r s t hr hs ht h1 h2 h3
  · exact diophantine_quadruple_extension_large_ratio a b c d ha hab hbc hcd
      hab2 hac2 hbc2 had2 hbd2 hcd2 r s t hr hs ht h1 h2

#print axioms solution
