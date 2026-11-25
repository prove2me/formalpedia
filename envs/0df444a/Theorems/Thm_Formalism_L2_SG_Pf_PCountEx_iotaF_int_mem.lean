-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_iotaF_int_mem
-- name    : Formalism.L2.SG.Pf.PCountEx.iotaF_int_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:38:37.682116+00:00
-- url     : https://prove2.me/theorems/c3cc58c9-df01-440a-b6ff-f73cb1783122
-- title:
--   PCount Ex: iota F int mem
-- statement:
--   The PCount Ex construction uses the iota F int mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IotaFIntMem.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IotaFIntMem.lean#L16-L22

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IotaFIntMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem Formalism.L2.SG.Pf.PCountEx.iotaF_int_mem (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    (A p).ιF (algebraMap (𝓞 F) F t) ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by sorry
