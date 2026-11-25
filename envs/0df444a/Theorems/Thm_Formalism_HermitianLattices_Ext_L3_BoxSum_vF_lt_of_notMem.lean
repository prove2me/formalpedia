-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_vF_lt_of_notMem
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.vF_lt_of_notMem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:30:04.756601+00:00
-- url     : https://prove2.me/theorems/9f335f02-c9b7-58b5-8001-aefbffc88fb8
-- title:
--   Box Sum: v F lt of not Mem
-- statement:
--   The Box Sum construction uses the v F lt of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NeBotOfIsMaximal.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NeBotOfIsMaximal.lean#L13-L22

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumPeriodic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_BoxInterEqEmpty
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeBotOfIsMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.vF_lt_of_notMem {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {e : ℕ} (h : n ∉ 𝔭 ^ e) : vF 𝔭 n < e := by sorry
