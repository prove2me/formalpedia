-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G2_exists_common
-- name    : Formalism.L2.SG.Pf.G2.exists_common
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:25.295253+00:00
-- url     : https://prove2.me/theorems/64c641c0-2868-477b-98d4-2007c5dde895
-- title:
--   G2: exists common
-- statement:
--   The G2 construction uses the exists common property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsSubDivMemSP.lean#L130-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsSubDivMemSP.lean#L130-L148

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsSubDivMemSP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_exists_common

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
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem Formalism.L2.SG.Pf.G2.exists_common {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι' : Type} (s : Finset ι') (r : ι' → K)
    (hr : haveI := h𝔭.isPrime; ∀ i ∈ s, r i ∈ HU.SP K 𝔭) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ i ∈ s, ∃ w : 𝓞 K, jK w = jK (ι t) * r i := by sorry
