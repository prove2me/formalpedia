-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_exists_den
-- name    : Formalism.L2.SG.Pf.LocalDenominators.exists_den
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:45.072098+00:00
-- url     : https://prove2.me/theorems/0f73ea87-f31b-5ba3-8883-fefc5545d1e7
-- title:
--   Local Denominators: exists den
-- statement:
--   The Local Denominators construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LocalDenominators.lean#L42-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LocalDenominators.lean#L42-L64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LocalDenominators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel Polynomial
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalDenominators
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem Formalism.L2.SG.Pf.LocalDenominators.exists_den {a : F} (ha : p.valuation F a ≤ 1) :
    ∃ t : 𝓞 F, t ∉ p.asIdeal ∧ ∃ y : 𝓞 F, (y : F) = (t : F) * a := by sorry
