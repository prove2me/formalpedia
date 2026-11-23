-- Prove2me | Theorems.Thm_CompanionTheory_FamInh_res_restrictScalars
-- name    : CompanionTheory.FamInh.res_restrictScalars
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:26.432514+00:00
-- url     : https://prove2.me/theorems/8e9298dd-dbef-44fb-bad6-f3783cafe9c5
-- title:
--   Fam Inh: res restrict Scalars
-- statement:
--   The Fam Inh construction uses the res restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L57-L60

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
omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

theorem CompanionTheory.FamInh.res_restrictScalars (g : Ω ≃ₐ[L] Ω) : AlgEquiv.restrictNormalHom L (g.restrictScalars K : G K Ω) = 1 := by sorry
