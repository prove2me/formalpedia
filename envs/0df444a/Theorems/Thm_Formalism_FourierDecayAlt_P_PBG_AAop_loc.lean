-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_AAop_loc
-- name    : Formalism.FourierDecayAlt.P.PBG.AAop_loc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:00:25.395928+00:00
-- url     : https://prove2.me/theorems/746e06b4-ef84-46e9-b764-de00fc5392c8
-- title:
--   PBG: AAop loc
-- statement:
--   The PBG construction uses the AAop loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L65-L73

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem Formalism.FourierDecayAlt.P.PBG.AAop_loc (hD : IsOpen D) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f f₂ : Q.Mx k r → E)
    (h : ∀ x ∈ Q.Glev k r 0 ∩ D, f x = f₂ x) (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ D) :
    C3.AAop k r m hm u f g = C3.AAop k r m hm u f₂ g := by sorry
