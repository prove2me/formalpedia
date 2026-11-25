-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_casimir_kronecker_sum
-- name    : CompanionTheory.Zuck.casimir_kronecker_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:01:52.359079+00:00
-- url     : https://prove2.me/theorems/87dd5479-3fb1-44bf-81d3-02efdc5a307f
-- title:
--   Zuck: casimir kronecker sum
-- statement:
--   The Zuck construction uses the casimir kronecker sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L64-L72

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem CompanionTheory.Zuck.casimir_kronecker_sum (n : ℕ) :
    (∑ a : Fin n, ∑ b : Fin n, Matrix.single a b (1 : ℂ) ⊗ₖ (-(Matrix.single b a (1 : ℂ))ᵀ) =
      (-1 : ℂ) • ((cM n)ᵀ * cM n)) ∧
    (∑ a : Fin n, ∑ b : Fin n, (-(Matrix.single a b (1 : ℂ))ᵀ) ⊗ₖ Matrix.single b a (1 : ℂ) =
      (-1 : ℂ) • ((cM n)ᵀ * cM n)) := by sorry
