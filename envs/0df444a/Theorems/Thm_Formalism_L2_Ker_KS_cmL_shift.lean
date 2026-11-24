-- Prove2me | Theorems.Thm_Formalism_L2_Ker_KS_cmL_shift
-- name    : Formalism.L2.Ker.KS.cmL_shift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:45.512784+00:00
-- url     : https://prove2.me/theorems/56b93f5d-09fa-49de-a021-72b38c5aab20
-- title:
--   KS: cm L shift
-- statement:
--   The KS construction uses the cm L shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L234-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/SelfDualLatticeNorms/HalfPeriodStandardCM.lean#L234-L281

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

theorem Formalism.L2.Ker.KS.cmL_shift (hs : 0 < (a : ℤ) + b + c) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    ∃ (lam' : ℂ) (hlam' : lam' ≠ 0),
      (cmL ((a : ℤ) + b + c).toNat (b + 2 * c) d (by omega) hd lam' hlam').lattice = (cmL a b d ha hd lam hlam).lattice := by sorry
