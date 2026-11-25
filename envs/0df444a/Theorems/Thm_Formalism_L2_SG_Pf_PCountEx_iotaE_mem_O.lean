-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_iotaE_mem_O
-- name    : Formalism.L2.SG.Pf.PCountEx.iotaE_mem_O
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:16:44.025849+00:00
-- url     : https://prove2.me/theorems/acc0b5a6-fa49-5c8f-81cd-a5462ac824da
-- title:
--   PCount Ex: iota E mem O
-- statement:
--   The PCount Ex construction uses the iota E mem O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/WithZeroLeOneEqExp.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/WithZeroLeOneEqExp.lean#L34-L38

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SimpLemmas
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
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

theorem Formalism.L2.SG.Pf.PCountEx.iotaE_mem_O (p : HeightOneSpectrum (𝓞 F)) (e : 𝓞 E) : (A p).ιE (e : E) ∈ (A p).O := by sorry
