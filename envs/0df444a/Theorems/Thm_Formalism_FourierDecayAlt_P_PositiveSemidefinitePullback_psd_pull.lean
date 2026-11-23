-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_psd_pull
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.psd_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:48.468835+00:00
-- url     : https://prove2.me/theorems/5ae83593-21e5-47da-8de4-ab3116153834
-- title:
--   Positive Semidefinite Pullback: psd pull
-- statement:
--   The Positive Semidefinite Pullback construction uses the psd pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveSemidefinitePullback.lean#L47-L49

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

theorem Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.psd_pull {α β : Type} {Y : Finset α} (g : α → β) {k : β → β → ℂ}
    (h : PSDOn (Y.image g) k) : PSDOn Y (fun p q => k (g p) (g q)) := by sorry
