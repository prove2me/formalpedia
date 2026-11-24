-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_CoefficientBoundLemmas_addVal_prod
-- name    : Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas.addVal_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:04.197253+00:00
-- url     : https://prove2.me/theorems/b14dcd8e-0032-4f06-a8cc-02b73668226b
-- title:
--   Coefficient Bound Lemmas: add Val prod
-- statement:
--   The Coefficient Bound Lemmas construction uses the add Val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/CoefficientBoundHolds.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/CoefficientBoundHolds.lean#L11-L17

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_CoefficientBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas.addVal_prod {ι : Type*} (s : Finset ι) (c : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, c i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (c i) := by sorry
