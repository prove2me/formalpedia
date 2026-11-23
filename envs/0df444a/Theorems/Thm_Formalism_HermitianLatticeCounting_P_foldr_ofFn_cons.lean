-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_foldr_ofFn_cons
-- name    : Formalism.HermitianLatticeCounting.P.foldr_ofFn_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:03:23.256005+00:00
-- url     : https://prove2.me/theorems/de5a623d-06b3-4fdc-81ab-2acd0aa23b88
-- title:
--   P: foldr of Fn cons
-- statement:
--   The P construction uses the foldr of Fn cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L996-L998
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L996-L998

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
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.foldr_ofFn_cons {W ι : Type} (Eop : ι → W → W) (q : ℕ) (i : ι) (τ : Fin q → ι) (w : W) :
    (List.ofFn (Fin.cons i τ : Fin (q + 1) → ι)).foldr Eop w = Eop i ((List.ofFn τ).foldr Eop w) := by sorry
