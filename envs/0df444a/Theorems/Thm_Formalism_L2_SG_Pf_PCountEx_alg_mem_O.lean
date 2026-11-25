-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_alg_mem_O
-- name    : Formalism.L2.SG.Pf.PCountEx.alg_mem_O
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:39:28.105591+00:00
-- url     : https://prove2.me/theorems/e0c0dac6-f8d6-58da-a8d7-d404f40a73e8
-- title:
--   PCount Ex: alg mem O
-- statement:
--   The PCount Ex construction uses the alg mem O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/WithZeroLeOneEqExp.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/WithZeroLeOneEqExp.lean#L40-L46

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

theorem Formalism.L2.SG.Pf.PCountEx.alg_mem_O (p : HeightOneSpectrum (𝓞 F)) {t : (A p).Fp} (ht : t ∈ (haveI := (A p).lf; 𝒪[(A p).Fp])) :
    algebraMap (A p).Fp (A p).Ep t ∈ (A p).O := by sorry
