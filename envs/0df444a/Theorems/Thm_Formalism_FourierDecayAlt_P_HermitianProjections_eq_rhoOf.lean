-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_eq_rhoOf
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.eq_rhoOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:11.968086+00:00
-- url     : https://prove2.me/theorems/e5262972-bcb0-49bd-a277-fb6c89677b3a
-- title:
--   Hermitian Projections: eq rho Of
-- statement:
--   The Hermitian Projections construction uses the eq rho Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L59-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L59-L72

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

theorem Formalism.FourierDecayAlt.P.HermitianProjections.eq_rhoOf (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det)
    (g : Matrix n n ℂ) (hg : g * V = V * Φ) (hgU : ∀ x, (Vᴴ * H) *ᵥ x = 0 → g *ᵥ x = x) :
    g = rhoOf H V Φ := by sorry
