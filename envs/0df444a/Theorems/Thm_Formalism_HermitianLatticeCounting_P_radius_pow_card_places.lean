-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_radius_pow_card_places
-- name    : Formalism.HermitianLatticeCounting.P.radius_pow_card_places
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:58.454432+00:00
-- url     : https://prove2.me/theorems/f04a35dc-9f09-483c-a912-d223d96ed81b
-- title:
--   P: radius pow card places
-- statement:
--   The P construction uses the radius pow card places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L447-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L447-L452

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

theorem Formalism.HermitianLatticeCounting.P.radius_pow_card_places (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) :
    idealRadius E aa ^ Fintype.card (InfinitePlace E) = √(FractionalIdeal.absNorm aa : ℝ) := by sorry
