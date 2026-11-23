-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pf_abs
-- name    : Formalism.FourierDecayAlt.P.Mx7.pf_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:10.243116+00:00
-- url     : https://prove2.me/theorems/2229cd9e-d757-435f-9186-4b1050272d68
-- title:
--   Mx7: pf abs
-- statement:
--   The Mx7 construction uses the pf abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L521-L562
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L521-L562

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section

theorem Formalism.FourierDecayAlt.P.Mx7.pf_abs (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1)
    (hq1 : q1.Monic) (hdeg : q1.natDegree = 2 * s.card + 2) (e : ℂ)
    (he : e = q1.nextCoeff - ∑ i ∈ s, ρ i - ∑ i ∈ s, (ρ i + 1)) :
    ∃ r : ℂ, ∀ Y : ℂ, (∀ i ∈ s, Y + ρ i ≠ 0) → (∀ i ∈ s, Y + (ρ i + 1) ≠ 0) →
      c * q1.eval Y * ((∏ i ∈ s, (Y + ρ i))⁻¹ * (∏ i ∈ s, (Y + (ρ i + 1)))⁻¹) =
        c * (Y * (Y + e)) + r - (∑ l ∈ s, M l * (Y + ρ l)⁻¹) + (∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹) := by sorry
