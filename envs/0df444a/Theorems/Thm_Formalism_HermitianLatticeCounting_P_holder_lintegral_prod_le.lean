-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_holder_lintegral_prod_le
-- name    : Formalism.HermitianLatticeCounting.P.holder_lintegral_prod_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:28.979271+00:00
-- url     : https://prove2.me/theorems/cddadca7-715e-4c7a-8f3e-c2c96b3ab3e2
-- title:
--   P: holder lintegral prod le
-- statement:
--   The P construction uses the holder lintegral prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L749-L765
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L749-L765

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
open scoped ENNReal

theorem Formalism.HermitianLatticeCounting.P.holder_lintegral_prod_le {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι)
    (g : ι → Ω → ℝ≥0∞) (B : ι → ℝ≥0∞) (hg : ∀ i ∈ s, Measurable (g i))
    (h : ∀ i ∈ s, ∫⁻ ω, g i ω ^ s.card ∂μ ≤ B i ^ s.card) :
    ∫⁻ ω, ∏ i ∈ s, g i ω ∂μ ≤ ∏ i ∈ s, B i := by sorry
