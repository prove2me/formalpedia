-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_psd_mul
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.psd_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:40.073731+00:00
-- url     : https://prove2.me/theorems/e8398b78-4fdc-42be-ab18-bbd5cfcbaeef
-- title:
--   Positive Semidefinite Pullback: psd mul
-- statement:
--   The Positive Semidefinite Pullback construction uses the psd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L43-L45

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

theorem Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.psd_mul {α : Type} {Y : Finset α} {k₁ k₂ : α → α → ℂ} (h₁ : PSDOn Y k₁) (h₂ : PSDOn Y k₂) :
    PSDOn Y (fun p q => k₁ p q * k₂ p q) := by sorry
