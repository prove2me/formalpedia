-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_psd_sum_nonneg
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.psd_sum_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:33.422134+00:00
-- url     : https://prove2.me/theorems/c27b8bb5-6d9c-4b48-b5c2-09740cff8521
-- title:
--   Positive Semidefinite Pullback: psd sum nonneg
-- statement:
--   The Positive Semidefinite Pullback construction uses the psd sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L51-L54

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

theorem Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.psd_sum_nonneg {α : Type} {Y : Finset α} {k : α → α → ℂ} (h : PSDOn Y k) :
    0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q).re := by sorry
