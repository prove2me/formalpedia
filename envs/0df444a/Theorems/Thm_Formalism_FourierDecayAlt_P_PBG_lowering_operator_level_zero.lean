-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_lowering_operator_level_zero
-- name    : Formalism.FourierDecayAlt.P.PBG.lowering_operator_level_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:24.086953+00:00
-- url     : https://prove2.me/theorems/dda5c0af-1cde-454c-800a-3f8d974c60e5
-- title:
--   PBG: lowering operator level zero
-- statement:
--   The PBG construction uses the lowering operator level zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L104-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L104-L115

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

theorem Formalism.FourierDecayAlt.P.PBG.lowering_operator_level_zero (hD : IsOpen D) (m : ℕ) (hm : m ≤ r) (ell : ℂ) (v : VS k r 0 D E) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r 0 ∩ D) :
    C3.AAvop k r m hm ell (v : Q.Mx k r → E) g =
      ((C3.AAv k r (E0 (E := E) hD) (y0 g) m hm ell) v : Q.Mx k r → E) g := by sorry
