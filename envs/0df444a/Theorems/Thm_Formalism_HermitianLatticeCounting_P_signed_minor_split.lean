-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_signed_minor_split
-- name    : Formalism.HermitianLatticeCounting.P.signed_minor_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:30.657795+00:00
-- url     : https://prove2.me/theorems/754172c0-a9cb-4985-9c8e-e5a7b11661db
-- title:
--   P: signed minor split
-- statement:
--   The P construction uses the signed minor split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L511-L518
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L511-L518

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.signed_minor_split {F : Type} [Field F] {p : ℕ} (s : Fin p → ℕ) (t : Fin p → F) (a : Fin p) :
    IndexedMinorEntry s t a = (∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t a' ^ s a') *
      (((ParitySign (s a) : ℤ) : F) * t a ^ s a) := by sorry
