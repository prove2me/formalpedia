-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_bz_of_sup
-- name    : Formalism.FourierDecayAlt.P.PBK.memLp_bz_of_sup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:05.05094+00:00
-- url     : https://prove2.me/theorems/e9ef956a-11aa-5a5a-a1d6-99ea3e731df4
-- title:
--   PBK: mem Lp bz of sup
-- statement:
--   The PBK construction uses the mem Lp bz of sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemLpBzOfSup.lean#L16-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemLpBzOfSup.lean#L16-L79

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemLpBzOfSup
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
open scoped ComplexConjugate InnerProductSpace ENNReal
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem Formalism.FourierDecayAlt.P.PBK.memLp_bz_of_sup {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS : ℝ) (memU : ∀ x : ℂ, x ≠ 0 → MemLp (ut x) 2 volume)
    (sup : ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut x D‖ ^ 2 ≤ SS) (hbt : StronglyMeasurable bt)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) K)
    (germ : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
      ∀ᵐ D, D ∈ K → ‖ut x D - mainD s β ε bt x D‖ ≤ C * ‖x‖⁻¹) :
    MemLp (bz s bt) 2 volume ∧ ∫ z, ‖bz s bt z‖ ^ 2 ≤ SS := by sorry
