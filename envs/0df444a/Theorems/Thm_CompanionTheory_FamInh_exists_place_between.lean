-- Prove2me | Theorems.Thm_CompanionTheory_FamInh_exists_place_between
-- name    : CompanionTheory.FamInh.exists_place_between
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:49.286001+00:00
-- url     : https://prove2.me/theorems/b1fe0cee-fd9f-4038-a762-75687d076379
-- title:
--   Fam Inh: exists place between
-- statement:
--   The Fam Inh construction uses the exists place between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L16-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open CompanionTheory CompanionTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
omit [IsAlgClosure K Ω]

theorem CompanionTheory.FamInh.exists_place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by sorry
