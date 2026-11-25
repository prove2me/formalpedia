-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LocalizedFibreSets_card_phi_succ
-- name    : Formalism.L2.SG.Pf.LocalizedFibreSets.card_phi_succ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:25.347488+00:00
-- url     : https://prove2.me/theorems/431bed2f-428c-533e-bb40-a643df1b755a
-- title:
--   Localized Fibre Sets: card phi succ
-- statement:
--   The Localized Fibre Sets construction uses the card phi succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardPhiSucc.lean#L64-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardPhiSucc.lean#L64-L238

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
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
  [Fact (IsFixF K F)] {m : ℕ}

theorem Formalism.L2.SG.Pf.LocalizedFibreSets.card_phi_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (a : Fin m → 𝓞 F) {k : ℕ} (hk : 1 ≤ k) (T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)))
    (hT : Tᴴ = T) (hT0 : ∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) :
    Nat.card {Y // phiQ K 𝔭 (k + 1) a Y = T} =
      Ideal.absNorm 𝔭 ^ (m * m) * Nat.card {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} := by sorry
