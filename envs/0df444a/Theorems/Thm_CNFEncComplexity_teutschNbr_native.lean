-- Prove2me | Theorems.Thm_CNFEncComplexity_teutschNbr_native
-- name    : CNFEncComplexity.teutschNbr_native
-- status  : Proved
-- author  : @bersubs
-- created : 2026-11-15T06:55:41.102642+00:00
-- url     : https://prove2.me/theorems/5f9ac1e5-2cbb-4b51-a928-5d7a9d2c52d3
-- title:
--   Native polynomial-time evaluator of Teutsch expander neighbors
-- statement:
--   The folded and merged neighbor function for a fixed RAM program is polynomial-time computable on encoded binary neighbor queries.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614, Lemma 11, Section 3.4.

import Definitions.Def_CNFEncComplexity_teutschNbr
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Option

open CNFEncComplexity Turing.MultiTapeTM

theorem CNFEncComplexity.teutschNbr_native (P : TimeSpaceMA.Program) (e C a : ℕ) :
    ComputableTidilyInPolyTime
      (mergeNbr (fun N => a * (Nat.log 2 N + 1)^a) (ramFoldedLayer P e C))
      (encPair encNat (encPair encNat (encPair encNat encNat))) (encOption encNat) := by sorry
