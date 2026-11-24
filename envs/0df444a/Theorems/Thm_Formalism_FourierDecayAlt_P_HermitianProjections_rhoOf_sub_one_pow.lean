-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_rhoOf_sub_one_pow
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.rhoOf_sub_one_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:42.898369+00:00
-- url     : https://prove2.me/theorems/487a737a-8d40-4b3f-8944-dfae997eb179
-- title:
--   Hermitian Projections: rho Of sub one pow
-- statement:
--   The Hermitian Projections construction uses the rho Of sub one pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L74-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L74-L88

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

theorem Formalism.FourierDecayAlt.P.HermitianProjections.rhoOf_sub_one_pow (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ)
    (hΓ : IsUnit (Vᴴ * H * V).det) (m : ℕ) :
    (rhoOf H V Φ - 1) ^ (m + 1) = V * (Φ - 1) ^ (m + 1) * prj H V := by sorry
