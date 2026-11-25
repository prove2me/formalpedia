-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_level_zero_derivative_rule
-- name    : Formalism.FourierDecayAlt.P.PBG.level_zero_derivative_rule
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:00:57.395914+00:00
-- url     : https://prove2.me/theorems/155efce0-37b5-4c1b-a9ca-60853e193386
-- title:
--   PBG: level zero derivative rule
-- statement:
--   The PBG construction uses the level zero derivative rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L126-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L126-L142

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

theorem Formalism.FourierDecayAlt.P.PBG.level_zero_derivative_rule (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g)
    (p q : Fin (2 * r + k + 1)) (hpq : C3.InNp k r p q) :
    E0 hD p q (vK hD K hK) = C3.dpsiP k r z' p q • vK hD K hK := by sorry
