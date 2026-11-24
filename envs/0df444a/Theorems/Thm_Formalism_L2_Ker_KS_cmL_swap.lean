-- Prove2me | Theorems.Thm_Formalism_L2_Ker_KS_cmL_swap
-- name    : Formalism.L2.Ker.KS.cmL_swap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:47.882115+00:00
-- url     : https://prove2.me/theorems/e00d1d85-ac8d-4da0-9665-c867a45439f6
-- title:
--   KS: cm L swap
-- statement:
--   The KS construction uses the cm L swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L191-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L191-L232

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
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)

theorem Formalism.L2.Ker.KS.cmL_swap (hc : 0 < c) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    ∃ (lam' : ℂ) (hlam' : lam' ≠ 0), (cmL c.toNat (-b) d (by omega) hd lam' hlam').lattice = (cmL a b d ha hd lam hlam).lattice := by sorry
