-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_embedded_ideal_points_separated
-- name    : Formalism.HermitianLatticeCounting.P.embedded_ideal_points_separated
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:51.761709+00:00
-- url     : https://prove2.me/theorems/a6343a6b-8c90-4026-827d-6602b38024d5
-- title:
--   P: embedded ideal points separated
-- statement:
--   The P construction uses the embedded ideal points separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L455-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L455-L467

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
open Classical

theorem Formalism.HermitianLatticeCounting.P.embedded_ideal_points_separated (hn : IdealNormProductLowerBound) (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) (S : Finset E)
    (hS : ∀ D ∈ S, D ∈ aa) : IsNormSeparated (idealRadius E aa) (S.image (infinitePlaceEmbedding E)) := by sorry
