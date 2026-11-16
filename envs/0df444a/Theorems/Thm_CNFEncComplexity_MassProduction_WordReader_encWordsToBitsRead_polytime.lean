-- Prove2me | Theorems.Thm_CNFEncComplexity_MassProduction_WordReader_encWordsToBitsRead_polytime
-- name    : CNFEncComplexity.MassProduction.WordReader.encWordsToBitsRead_polytime
-- status  : Proved
-- author  : @bersubs
-- created : 2026-11-15T06:43:55.926577+00:00
-- url     : https://prove2.me/theorems/7e3a1300-ab03-4efd-b1bc-c223a22b8efe
-- title:
--   Polynomial-time conversion of delimited words to framed bits
-- statement:
--   Words over the ternary delimiter format can be read into the framed binary list encoding in polynomial time.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614, Lemma 11, Section 3.4.

import Definitions.Def_CNFEncComplexity_encWords
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Mathlib.Computability.TuringMachine.Computable

open CNFEncComplexity Turing.MultiTapeTM

theorem CNFEncComplexity.MassProduction.WordReader.encWordsToBitsRead_polytime {α : Type} (words : α → List (List Bool)) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun a => encWords (words a)) (encList encBits) words) := by sorry
