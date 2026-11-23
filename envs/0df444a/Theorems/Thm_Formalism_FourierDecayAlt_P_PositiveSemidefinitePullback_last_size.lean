-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_last_size
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.last_size
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:42.518809+00:00
-- url     : https://prove2.me/theorems/fd3c8222-503d-41dd-82b5-7cfe559212b7
-- title:
--   Positive Semidefinite Pullback: last size
-- statement:
--   The Positive Semidefinite Pullback construction uses the last size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L58-L67

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
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.last_size (T : Tower E) {i : ℕ} (hi : 1 ≤ i) {p : Pt E} (hp : p ∈ T.X i) :
    ∃ s ∈ Icc 1 i, p.getLast?.map Prod.fst = some s := by sorry
