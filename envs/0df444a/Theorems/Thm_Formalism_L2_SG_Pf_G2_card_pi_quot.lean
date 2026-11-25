-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G2_card_pi_quot
-- name    : Formalism.L2.SG.Pf.G2.card_pi_quot
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:43.111052+00:00
-- url     : https://prove2.me/theorems/77575048-789b-5731-b008-59eff1c5b990
-- title:
--   G2: card pi quot
-- statement:
--   The G2 construction uses the card pi quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardQuotSmulTopCongr.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardQuotSmulTopCongr.lean#L74-L86

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsSubDivMemSP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardQuotSmulTopCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G2
open Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.L2.SG.Pf.G2.card_pi_quot (𝔭 : Ideal (𝓞 F)) {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ → ℕ) (j : ℕ) :
    Nat.card ((∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i) ⧸
        (extP K 𝔭 ^ j • ⊤ : Submodule (𝓞 K) (∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i))) =
      Ideal.absNorm (extP K 𝔭) ^ ∑ i, min (e i) j := by sorry
