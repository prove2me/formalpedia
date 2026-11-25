-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_relIndex_eq
-- name    : Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:09.423564+00:00
-- url     : https://prove2.me/theorems/299300f3-74af-5281-919e-00e206591ace
-- title:
--   Idx K: rel Index eq
-- statement:
--   The Idx K construction uses the rel Index eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L406-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L406-L437

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
variable {K : Type} [Field K] [NumberField K]
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]

theorem Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_eq (n : ℕ) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (N : Submodule (𝓞 K) M) (hN : N.FG) (hD : HDep n N)
    (ι : (Fin n → 𝓞 K) →ₗ[𝓞 K] M) (hι : Function.Injective ι) (hιN : LinearMap.range ι ≤ N) (d : 𝓞 K) (hd : d ≠ 0)
    (hdN : Ideal.span {d} • N ≤ LinearMap.range ι) :
    (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup = Ideal.absNorm 𝔞 ^ n := by sorry
