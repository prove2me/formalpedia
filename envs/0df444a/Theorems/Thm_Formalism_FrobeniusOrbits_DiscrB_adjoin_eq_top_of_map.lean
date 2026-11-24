-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_adjoin_eq_top_of_map
-- name    : Formalism.FrobeniusOrbits.DiscrB.adjoin_eq_top_of_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:59.048774+00:00
-- url     : https://prove2.me/theorems/9c01d5f1-dae2-432a-8aa0-a3d30a95d0b5
-- title:
--   Discr B: adjoin eq top of map
-- statement:
--   The Discr B construction uses the adjoin eq top of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscrB.lean#L21-L30

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.DiscrB
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L]

theorem Formalism.FrobeniusOrbits.DiscrB.adjoin_eq_top_of_map {K : Type} [Field K] [Algebra ℚ K] (ι : K →ₐ[ℚ] L) (S : Set K)
    (T : IntermediateField ℚ L) (hS : adjoin ℚ (ι '' S) = T) (hx : ∀ x : K, ι x ∈ T) :
    adjoin ℚ S = ⊤ := by sorry
