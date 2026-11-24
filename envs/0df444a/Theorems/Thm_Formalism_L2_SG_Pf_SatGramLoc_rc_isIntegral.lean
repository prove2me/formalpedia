-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_rc_isIntegral
-- name    : Formalism.L2.SG.Pf.SatGramLoc.rc_isIntegral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:23.433378+00:00
-- url     : https://prove2.me/theorems/f87a0042-cca5-4782-92eb-b9ecfbec6f7a
-- title:
--   Sat Gram Loc: rc is Integral
-- statement:
--   The Sat Gram Loc construction uses the rc is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfB.lean#L23-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfB.lean#L23-L44

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Formalism.L2.SG.Pf.SatGramLoc.rc_isIntegral (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F)
    (hx : x ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
      (v.adicCompletionIntegers F).toSubring) :
    letI := rcIntAlg (E := E) v
    IsIntegral (v.adicCompletionIntegers F) x := by sorry
