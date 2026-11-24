-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_sub_left
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.herm_sub_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:57:09.348912+00:00
-- url     : https://prove2.me/theorems/1440cf4d-c3e3-47ac-b74e-bf2a7370575e
-- title:
--   Hermitian Projections: herm sub left
-- statement:
--   The Hermitian Projections construction uses the herm sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L137-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L137-L138

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

theorem Formalism.FourierDecayAlt.P.HermitianProjections.herm_sub_left (H : Matrix n n ℂ) (a b w : n → ℂ) : herm H (a - b) w = herm H a w - herm H b w := by sorry
