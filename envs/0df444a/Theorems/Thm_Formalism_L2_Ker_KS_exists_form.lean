-- Prove2me | Theorems.Thm_Formalism_L2_Ker_KS_exists_form
-- name    : Formalism.L2.Ker.KS.exists_form
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:23:04.587397+00:00
-- url     : https://prove2.me/theorems/69b09132-a762-4e3c-a80b-ba207b765ee5
-- title:
--   KS: exists form
-- statement:
--   The KS construction uses the exists form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L348-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L348-L384

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Ker Formalism.L2.Ker.KS
open Formalism.L2.Th1.H (cmL CmOK)

theorem Formalism.L2.Ker.KS.exists_form (d : ℕ) (hd : 0 < d) (L : PeriodPair) (hst : ∀ x ∈ L.lattice, Formalism.L2.Th1.F.cmTheta 1 d * x ∈ L.lattice) :
    ∃ (a : ℕ) (b c : ℤ) (ha : 0 < a) (lam : ℂ) (hlam : lam ≠ 0), 4 * (a : ℤ) * c = b ^ 2 + d ∧
      (cmL a b d ha hd lam hlam).lattice = L.lattice := by sorry
