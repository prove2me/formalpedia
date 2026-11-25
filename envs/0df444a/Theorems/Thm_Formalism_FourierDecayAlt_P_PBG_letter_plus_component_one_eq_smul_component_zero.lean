-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_letter_plus_component_one_eq_smul_component_zero
-- name    : Formalism.FourierDecayAlt.P.PBG.letter_plus_component_one_eq_smul_component_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:15.905476+00:00
-- url     : https://prove2.me/theorems/0bc5bde1-2f3f-4dfd-a951-6c28c403c2ac
-- title:
--   PBG: letter plus component one eq smul component zero
-- statement:
--   The PBG construction uses the letter plus component one eq smul component zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L225-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean#L225-L240

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

theorem Formalism.FourierDecayAlt.P.PBG.letter_plus_component_one_eq_smul_component_zero (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (hs : 1 ≤ s) (hj : i0 + s ≤ r)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ) (hdet : hh.det ≠ 0) (hτ : τ ≠ 0) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g) (Y : ℝ) :
    Formalism.FourierDecayAlt.D.vLet k r z z' (i0 + s) hj (true, Y) 1 K x₁ =
      ((-1 : ℂ) ^ (s - 1) * τ⁻¹) • Formalism.FourierDecayAlt.D.vLet k r z z' i0 (by omega) (true, Y) 0 K x₁ := by sorry
