-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_sum_pts
-- name    : Formalism.FourierDecayAlt.P.BlockStartPoints.sum_pts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:21.278729+00:00
-- url     : https://prove2.me/theorems/23262017-4422-4cf4-ad08-030b2deb4089
-- title:
--   Block Start Points: sum pts
-- statement:
--   The Block Start Points construction uses the sum pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L95-L102

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.BlockStartPoints.sum_pts {β : Type} [AddCommMonoid β] (Y : Finset (Pt E)) (s : ℕ) (S : Finset E)
    (F : Pt E → β) : ∑ p ∈ pts Y s S, F p = ∑ t ∈ S, ∑ h ∈ Y, F (join h s t) := by sorry
