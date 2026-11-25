-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_approxF
-- name    : Formalism.L2.SG.Pf.PCountEx.approxF
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:02.687008+00:00
-- url     : https://prove2.me/theorems/f7e5cfc3-09ce-471b-810a-4ece1a7d52e9
-- title:
--   PCount Ex: approx F
-- statement:
--   The PCount Ex construction uses the approx F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/WithZeroLeOneEqExp.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/WithZeroLeOneEqExp.lean#L21-L25

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SimpLemmas
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Theorems.Thm_UpperTheory_Reformulated_B_ApproximationIntegralOutsideFinset_approxF

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

theorem Formalism.L2.SG.Pf.PCountEx.approxF (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0) (b : ∀ p, (A p).Fp) :
    ∃ f : F, (∀ p ∈ S, haveI := (A p).lf
        valuation (A p).Fp ((A p).ιF f - b p) ≤ valuation (A p).Fp ((A p).ιF (algebraMap (𝓞 F) F c))) ∧
      ∀ p ∉ S, (A p).ιF f ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by sorry
