-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_prj_perp
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.prj_perp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:11.780813+00:00
-- url     : https://prove2.me/theorems/92c70093-d578-4311-82fd-1e600ef8ba54
-- title:
--   Hermitian Projections: prj perp
-- statement:
--   The Hermitian Projections construction uses the prj perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L33-L37

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

theorem Formalism.FourierDecayAlt.P.HermitianProjections.prj_perp (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (x : n → ℂ) (hx : (Vᴴ * H) *ᵥ x = 0) :
    prj H V *ᵥ x = 0 := by sorry
