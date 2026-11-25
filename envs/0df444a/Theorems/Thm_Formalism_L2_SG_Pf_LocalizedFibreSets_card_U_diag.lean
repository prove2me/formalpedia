-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LocalizedFibreSets_card_U_diag
-- name    : Formalism.L2.SG.Pf.LocalizedFibreSets.card_U_diag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:57.094804+00:00
-- url     : https://prove2.me/theorems/2ae23a81-c20d-5974-84d7-3388c50a8aba
-- title:
--   Localized Fibre Sets: card U diag
-- statement:
--   The Localized Fibre Sets construction uses the card U diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/PhiCountingHolds.lean#L48-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/PhiCountingHolds.lean#L48-L91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsoCountOneInert
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_PhiCountingHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)]

theorem Formalism.L2.SG.Pf.LocalizedFibreSets.card_U_diag (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : ι → 𝓞 F) (hb : ∀ i, b i ∉ 𝔭) :
    (Nat.card {γ : Matrix ι ι (𝓞 K ⧸ extP K 𝔭 ^ 1) //
      γᴴ * diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i))) * γ =
        diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i)))} : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (Fintype.card ι ^ 2) * alphaStd K 𝔭 (Fintype.card ι) := by sorry
