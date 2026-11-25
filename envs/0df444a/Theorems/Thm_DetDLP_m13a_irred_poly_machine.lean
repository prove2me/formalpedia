-- Prove2me | Theorems.Thm_DetDLP_m13a_irred_poly_machine
-- name    : DetDLP.m13a_irred_poly_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T01:40:03.658481+00:00
-- url     : https://prove2.me/theorems/bd73cb8c-78e4-4571-96b4-77292ea64343
-- title:
--   Deterministic polynomial-time search for a binary irreducible modulus with unary padding
-- statement:
--   The padded bit-word finder is polynomial-time on all inputs. For any positive degree, its canonical unpadded search returns a monic integer polynomial of that degree with irreducible reduction modulo two. If the budget (word length) is at least two raised to the requested degree (number of true bits), the two algorithms return exactly the same coefficient word.

import Definitions.Def_DetDLP_M13A_IrredHermite
import Definitions.Def_ToTuring_PolyT
open DetDLP_M13A_IrredHermite Polynomial

theorem DetDLP.m13a_irred_poly_machine :
    Groundwork.PolyT irredMachine ∧
    (∀ κ : ℕ, 0 < κ → let f := polynomial ℤ (findIrredPoly κ)
      f.Monic ∧ f.natDegree = κ ∧ Irreducible (f.map (Int.castRingHom (ZMod 2)))) ∧
    ∀ w : List Bool, let κ := (w.filter id).length
      2 ^ κ ≤ w.length → irredMachine w = findIrredPoly κ := by sorry
