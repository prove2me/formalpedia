-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_letter_plus_component_one
-- name    : Formalism.FourierDecayAlt.P.PBG.letter_plus_component_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:57.037955+00:00
-- url     : https://prove2.me/theorems/aa04a81e-d4c4-4b01-a0af-33946eafe2d3
-- title:
--   PBG: letter plus component one
-- statement:
--   The PBG construction uses the letter plus component one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L176-L183

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

theorem Formalism.FourierDecayAlt.P.PBG.letter_plus_component_one (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (hj1 : 1 ≤ j) (Y : ℝ) (f : Q.Mx k r → E)
    (g : Q.Mx k r) :
    Formalism.FourierDecayAlt.D.vLet k r z z' j hj (true, Y) 1 f g =
      (Dmin k r z z' g ⟨j, by omega⟩)⁻¹ • C3.AAop k r (j - 1) (by omega) ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) f g := by sorry
