-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_placeEmbedding_sub
-- name    : Formalism.HermitianLatticeCounting.P.norm_placeEmbedding_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:26.016584+00:00
-- url     : https://prove2.me/theorems/f2e15cd3-c438-46cc-92e2-62b1a36f69a4
-- title:
--   P: norm place Embedding sub
-- statement:
--   The P construction uses the norm place Embedding sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L409-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L409-L411

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

theorem Formalism.HermitianLatticeCounting.P.norm_placeEmbedding_sub (E : Type) [Field E] (x y : E) (w : InfinitePlace E) :
    ‖infinitePlaceEmbedding E x w - infinitePlaceEmbedding E y w‖ = w (x - y) := by sorry
