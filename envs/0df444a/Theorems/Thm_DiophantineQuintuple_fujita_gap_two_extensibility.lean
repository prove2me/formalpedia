-- Prove2me | Theorems.Thm_DiophantineQuintuple_fujita_gap_two_extensibility
-- name    : DiophantineQuintuple.fujita_gap_two_extensibility
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-23T15:41:58.375935+00:00
-- url     : https://prove2.me/theorems/615057b2-a23a-4226-8991-bd7f8a88a0dd
-- title:
--   Fujita 2008: no distance-two Diophantine pair extends to a quintuple
-- statement:
--   Y. Fujita ("The extensibility of Diophantine pairs {k-1,k+1}", J. Number Theory 128 (2008)): no Diophantine pair {a, a+2} is contained in a Diophantine quintuple. The proof uses linear forms in logarithms (Baker's method); no elementary proof is known. Used in Cipu-Fujita Glas. Mat. 50 (2015) to license the gap-two case.
-- source:
--   Decomposition of diophantine_no_consecutive_gap_two, Prove2Me There is no Diophantine quintuple mission

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

namespace DiophantineQuintuple

theorem fujita_gap_two_extensibility (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) (h2 : f 1 = f 0 + 2) : False := by sorry

end DiophantineQuintuple
