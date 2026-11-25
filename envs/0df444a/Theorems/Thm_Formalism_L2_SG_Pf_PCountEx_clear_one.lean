-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_clear_one
-- name    : Formalism.L2.SG.Pf.PCountEx.clear_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:38:27.132608+00:00
-- url     : https://prove2.me/theorems/afcfc047-04f4-42c6-80eb-894ca93411bb
-- title:
--   PCount Ex: clear one
-- statement:
--   The PCount Ex construction uses the clear one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IotaFIntMem.lean#L111-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IotaFIntMem.lean#L111-L169

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

theorem Formalism.L2.SG.Pf.PCountEx.clear_one (p : HeightOneSpectrum (𝓞 F)) (z : (A p).Ep) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F t)) * z ∈ (A p).O := by sorry
