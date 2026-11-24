-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelGenB_exists_int_close
-- name    : Formalism.MainNotions.BridgeLevelGenB.exists_int_close
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:41:26.496776+00:00
-- url     : https://prove2.me/theorems/aae141eb-5ef0-4b28-b86b-21747aaaf55d
-- title:
--   Bridge Level Gen B: exists int close
-- statement:
--   The Bridge Level Gen B construction uses the exists int close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGenB.lean#L17-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGenB.lean#L17-L55

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.MainNotions.BridgeLevelGenB.exists_int_close (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (hx : Valued.v x ≤ 1)
    {g : 𝓞 F} (hg : g ≠ 0) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < v.intValuation g := by sorry
