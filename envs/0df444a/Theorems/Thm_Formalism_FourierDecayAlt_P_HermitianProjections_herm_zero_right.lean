-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_zero_right
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.herm_zero_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:28:57.295928+00:00
-- url     : https://prove2.me/theorems/207df742-eb46-5cfa-acaf-17c46d87ec54
-- title:
--   Hermitian Projections: herm zero right
-- statement:
--   The Hermitian Projections construction uses the herm zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L146-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L146-L147

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
variable {n : Type*} [Fintype n]

theorem Formalism.FourierDecayAlt.P.HermitianProjections.herm_zero_right (H : Matrix n n ℂ) (v : n → ℂ) : herm H v 0 = 0 := by sorry
