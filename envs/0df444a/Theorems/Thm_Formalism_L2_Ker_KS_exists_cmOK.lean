-- Prove2me | Theorems.Thm_Formalism_L2_Ker_KS_exists_cmOK
-- name    : Formalism.L2.Ker.KS.exists_cmOK
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:06.014836+00:00
-- url     : https://prove2.me/theorems/15fe470c-760a-40c3-bac4-8426370cc82b
-- title:
--   KS: exists cm OK
-- statement:
--   The KS construction uses the exists cm OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L386-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L386-L428

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

theorem Formalism.L2.Ker.KS.exists_cmOK (d : ℕ) (hd : 0 < d) (hd8 : d % 8 = 7) (hp : d.Prime) (L : PeriodPair)
    (hst : ∀ x ∈ L.lattice, Formalism.L2.Th1.F.cmTheta 1 d * x ∈ L.lattice) :
    ∃ (a : ℕ) (b c : ℤ) (ha : 0 < a) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d ∧ (cmL a b d ha hd lam hlam).lattice = L.lattice := by sorry
