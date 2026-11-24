-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_herm_smul_right
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.herm_smul_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:56:56.722683+00:00
-- url     : https://prove2.me/theorems/f0127401-840d-4e29-b141-af0f9d056017
-- title:
--   Hermitian Projections: herm smul right
-- statement:
--   The Hermitian Projections construction uses the herm smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L133-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L133-L135

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

theorem Formalism.FourierDecayAlt.P.HermitianProjections.herm_smul_right (H : Matrix n n ℂ) (c : ℂ) (v a : n → ℂ) : herm H v (c • a) = conj c * herm H v a := by sorry
