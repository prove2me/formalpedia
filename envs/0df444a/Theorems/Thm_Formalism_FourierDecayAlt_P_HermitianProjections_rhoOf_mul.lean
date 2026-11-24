-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_rhoOf_mul
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.rhoOf_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:21.753389+00:00
-- url     : https://prove2.me/theorems/2a0cb0cb-8419-4d93-b7c8-f5a8f63886a7
-- title:
--   Hermitian Projections: rho Of mul
-- statement:
--   The Hermitian Projections construction uses the rho Of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L46-L51

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

theorem Formalism.FourierDecayAlt.P.HermitianProjections.rhoOf_mul (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) :
    rhoOf H V Φ * V = V * Φ := by sorry
