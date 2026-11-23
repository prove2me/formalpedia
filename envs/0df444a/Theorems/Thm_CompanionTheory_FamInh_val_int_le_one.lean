-- Prove2me | Theorems.Thm_CompanionTheory_FamInh_val_int_le_one
-- name    : CompanionTheory.FamInh.val_int_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:30.267138+00:00
-- url     : https://prove2.me/theorems/55e940d8-8a33-4af1-9a1c-34429874f962
-- title:
--   Fam Inh: val int le one
-- statement:
--   The Fam Inh construction uses the val int le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L73-L75

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
variable [IsGalois K L]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
omit [IsAlgClosure K Ω] [IsAlgClosure L Ω]

theorem CompanionTheory.FamInh.val_int_le_one (A : ValuationSubring Ω) (x : 𝓞 L) : A.valuation (algebraMap L Ω (x : L)) ≤ 1 := by sorry
