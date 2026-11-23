-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_Sf_pts
-- name    : Formalism.FourierDecayAlt.P.BlockStartPoints.Sf_pts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:10.168717+00:00
-- url     : https://prove2.me/theorems/fcea51cf-15d7-463b-8c33-1ad00e8a8bcb
-- title:
--   Block Start Points: Sf pts
-- statement:
--   The Block Start Points construction uses the Sf pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L152-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L152-L160

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

theorem Formalism.FourierDecayAlt.P.BlockStartPoints.Sf_pts (D : Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Y : Finset (Pt E)) (S : Finset E) :
    D.Sf ε i w (pts Y s S) / D.wt w =
      ∑ t ∈ S, ∑ t' ∈ S, (D.Nst ε i s w Y (blk (D.Kr i) s t t') t t').re := by sorry
