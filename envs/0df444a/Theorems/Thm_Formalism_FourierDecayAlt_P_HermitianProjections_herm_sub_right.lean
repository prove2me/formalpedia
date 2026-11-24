-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_sub_right
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.herm_sub_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:57:01.006321+00:00
-- url     : https://prove2.me/theorems/86ae5f40-980f-4f04-a18a-7f1b3ca57f98
-- title:
--   Hermitian Projections: herm sub right
-- statement:
--   The Hermitian Projections construction uses the herm sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L140-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L140-L141

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

theorem Formalism.FourierDecayAlt.P.HermitianProjections.herm_sub_right (H : Matrix n n ℂ) (v a b : n → ℂ) : herm H v (a - b) = herm H v a - herm H v b := by sorry
