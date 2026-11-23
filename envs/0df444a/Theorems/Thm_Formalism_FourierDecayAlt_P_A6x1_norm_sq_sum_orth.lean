-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x1_norm_sq_sum_orth
-- name    : Formalism.FourierDecayAlt.P.A6x1.norm_sq_sum_orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:23.929796+00:00
-- url     : https://prove2.me/theorems/e1454cda-f0f9-4182-a942-afd9e9dc9ef2
-- title:
--   A6x1: norm sq sum orth
-- statement:
--   The A6x1 construction uses the norm sq sum orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialMeansOrthogonal.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialMeansOrthogonal.lean#L9-L21

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialMeansOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x1

theorem Formalism.FourierDecayAlt.P.A6x1.norm_sq_sum_orth {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : Type}
    [Fintype A] (P : A → E) (e₁ : A → ℂ) (he : ∀ ρ, ‖e₁ ρ‖ = 1)
    (h : ∀ ρ ρ', ρ ≠ ρ' → inner ℂ (P ρ) (P ρ') = 0) :
    ‖∑ ρ, e₁ ρ • P ρ‖ ^ 2 = ∑ ρ, ‖P ρ‖ ^ 2 := by sorry
