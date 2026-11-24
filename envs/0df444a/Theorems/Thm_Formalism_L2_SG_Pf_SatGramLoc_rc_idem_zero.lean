-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_rc_idem_zero
-- name    : Formalism.L2.SG.Pf.SatGramLoc.rc_idem_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:24.484897+00:00
-- url     : https://prove2.me/theorems/acff4d2a-bc73-4cdf-8f15-c64468189888
-- title:
--   Sat Gram Loc: rc idem zero
-- statement:
--   The Sat Gram Loc construction uses the rc idem zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfB.lean#L46-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfB.lean#L46-L111

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

theorem Formalism.L2.SG.Pf.SatGramLoc.rc_idem_zero (v : HeightOneSpectrum (𝓞 F)) (f t : E ⊗[F] v.adicCompletion F)
    (c : v.adicCompletion F) (hc : Valued.v c < 1) (hf : f * f = f)
    (hft : f = ((1 : E) ⊗ₜ[F] c) * t)
    (ht : letI := rcIntAlg (E := E) v; IsIntegral (v.adicCompletionIntegers F) t) : f = 0 := by sorry
