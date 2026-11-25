-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integral_bz_Q_le
-- name    : Formalism.FourierDecayAlt.P.PBK.integral_bz_Q_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:44.25014+00:00
-- url     : https://prove2.me/theorems/29b23417-954b-58ed-b4fd-8f7592713232
-- title:
--   PBK: integral bz Q le
-- statement:
--   The PBK construction uses the integral bz Q le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L101-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L101-L201

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem Formalism.FourierDecayAlt.P.PBK.integral_bz_Q_le {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS : ℝ) (memU : ∀ x : ℂ, x ≠ 0 → MemLp (ut x) 2 volume)
    (sup : ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut x D‖ ^ 2 ≤ SS) (hbt : StronglyMeasurable bt) (Q : Set ℂ)
    (hQ : IsCompact Q) (hloc : IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) {z | ε⁻¹ * z ^ s ∈ Q}) (C : ℝ)
    (hC : ∀ x : ℂ, x ≠ 0 → ∀ᵐ D, D ∈ Q → ‖ut x D - mainD s β ε bt x D‖ ≤ C * ‖x‖⁻¹) :
    ∫ z, ‖({z | ε⁻¹ * z ^ s ∈ Q}.indicator (bz s bt)) z‖ ^ 2 ≤ SS := by sorry
