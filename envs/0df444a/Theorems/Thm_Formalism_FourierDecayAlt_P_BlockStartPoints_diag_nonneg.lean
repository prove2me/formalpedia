-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_diag_nonneg
-- name    : Formalism.FourierDecayAlt.P.BlockStartPoints.diag_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:12.312467+00:00
-- url     : https://prove2.me/theorems/12d53793-65d9-4da3-910d-c9563e580bb4
-- title:
--   Block Start Points: diag nonneg
-- statement:
--   The Block Start Points construction uses the diag nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L140-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L140-L150

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

theorem Formalism.FourierDecayAlt.P.BlockStartPoints.diag_nonneg (D : Data E W) (hG : D.GramPSD) (hK : D.KernelPSD) (hW : D.WordsPos) (ε : ℝ)
    (hε : 0 < ε) (i s : ℕ) (w : W) (Y : Finset (Pt E)) (t : E) :
    0 ≤ (D.Nst ε i s w Y (blk (D.Kr i) s t t) t t).re := by sorry
