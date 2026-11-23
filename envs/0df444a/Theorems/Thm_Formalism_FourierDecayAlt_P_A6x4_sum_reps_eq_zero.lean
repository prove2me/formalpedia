-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_sum_reps_eq_zero
-- name    : Formalism.FourierDecayAlt.P.A6x4.sum_reps_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:50.921716+00:00
-- url     : https://prove2.me/theorems/7c38a5d3-1ceb-4e57-9442-f23b3d0d96bc
-- title:
--   A6x4: sum reps eq zero
-- statement:
--   The A6x4 construction uses the sum reps eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L13-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L13-L55

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.A6x4.sum_reps_eq_zero {L₁ L₂ : AddSubgroup K} {S : Finset K} (hle : L₁ ≤ L₂)
    (hS : IsReps S L₂ L₁) (f : K → ℂ) (hmul : ∀ x ∈ L₂, ∀ y ∈ L₂, f (x + y) = f x * f y)
    (h1 : ∀ l ∈ L₁, f l = 1) {l₀ : K} (hl₀ : l₀ ∈ L₂) (hne : f l₀ ≠ 1) : ∑ σ ∈ S, f σ = 0 := by sorry
