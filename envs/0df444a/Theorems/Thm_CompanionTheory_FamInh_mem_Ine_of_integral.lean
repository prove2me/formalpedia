-- Prove2me | Theorems.Thm_CompanionTheory_FamInh_mem_Ine_of_integral
-- name    : CompanionTheory.FamInh.mem_Ine_of_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:51.864798+00:00
-- url     : https://prove2.me/theorems/d43dff25-0378-4265-9fc1-f5cf56b29a00
-- title:
--   Fam Inh: mem Ine of integral
-- statement:
--   The Fam Inh construction uses the mem Ine of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L31-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L31-L47

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

theorem CompanionTheory.FamInh.mem_Ine_of_integral {A : ValuationSubring Ω} {σ : G K Ω} (hσ : σ ∈ Dec (F := K) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := K) A := by sorry
