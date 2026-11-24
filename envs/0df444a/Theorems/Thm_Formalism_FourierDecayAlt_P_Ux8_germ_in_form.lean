-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_germ_in_form
-- name    : Formalism.FourierDecayAlt.P.Ux8.germ_in_form
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:37:02.722554+00:00
-- url     : https://prove2.me/theorems/c0c9c1ce-55ee-460e-836c-607c99b3ca74
-- title:
--   Ux8: germ in form
-- statement:
--   The Ux8 construction uses the germ in form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L222-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SeminormCompletion.lean#L222-L258

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8

theorem Formalism.FourierDecayAlt.P.Ux8.germ_in_form (hG : G.GermRate) (hD : G.DetMatch) (hU : UseDerivBound) (hS : ScaleMatch) :
    ∃ (C₂ : ℕ) (Cc : ℝ),
    ∀ (k p m ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ι : Type) [Fintype ι]
    (U : UData k p (m+1+1) ρ Wp Wq ι), U.Ok C₂ →
    ∀ A₀ : ℝ, Cc * (((p + (m+1+1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (U.As : ℝ) ≤ A₀ →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc → ∃ Cst : ℝ,
    ∀ (bet : (B.Mat k ρ → ι → (Wq →L[ℂ] Wp)) → (B.Mat k ρ → ι → (Wq →L[ℂ] Wp)) → ℂ) (Cp : ℝ), 0 ≤ Cp →
      PosP bet (U.a C₂ A₀) U.mmB U.S → LBound bet U.AB U.mmB U.S Cp →
      (∀ x y x' y' : B.Mat k ρ → ι → (Wq →L[ℂ] Wp), (∀ g ∈ B.GV k ρ, x g = x' g) → (∀ g ∈ B.GV k ρ, y g = y' g) →
        bet x y = bet x' y') →
      ∀ (f : B.Mat k (p + (m+1+1) + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * U.As) f c →
      ∃ (V' : Type) (_ : NormedAddCommGroup V') (_ : NormedSpace ℂ V'), CompleteSpace V' ∧ ∃ Φ' : G.Mat (m+1+1) → V',
        (∀ (J : Finset (G.Mat (m+1+1))) (w : G.Mat (m+1+1) → ℂ), (∀ Z ∈ J, G.detM Z ≠ 0) →
          ‖∑ Z ∈ J, w Z • Φ' Z‖ ^ 2 = (bet (∑ Z ∈ J, w Z • U.Phi f Z) (∑ Z ∈ J, w Z • U.Phi f Z)).re) ∧
        ∀ t c' : ℂ, t ≠ 0 → c' * t ^ (m+1) ∈ Kc →
          ‖G.remainder betaU m (fun _ => 1) Φ' t c'‖ ≤ Cst * Cp * c * ‖t‖ := by sorry
