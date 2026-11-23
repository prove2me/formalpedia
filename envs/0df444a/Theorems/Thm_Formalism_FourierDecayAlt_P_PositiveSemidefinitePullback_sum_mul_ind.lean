-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_sum_mul_ind
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.sum_mul_ind
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:51.385557+00:00
-- url     : https://prove2.me/theorems/ec64d641-ca1b-4a53-9bb2-fe9ae4eea94c
-- title:
--   Positive Semidefinite Pullback: sum mul ind
-- statement:
--   The Positive Semidefinite Pullback construction uses the sum mul ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L22-L27

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.sum_mul_ind {α : Type} (Y A : Finset α) (hA : A ⊆ Y) (g : α → ℂ) :
    ∑ q : Y, g q * ind Y A q = ∑ q ∈ A, g q := by sorry
