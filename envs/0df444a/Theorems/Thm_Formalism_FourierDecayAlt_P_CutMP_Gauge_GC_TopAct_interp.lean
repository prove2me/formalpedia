-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAct_interp
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct.interp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:38.4518+00:00
-- url     : https://prove2.me/theorems/0bfcf467-bd80-53ae-8f38-a22138e7ec4b
-- title:
--   Top Act: interp
-- statement:
--   The Top Act construction uses the interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTRTopActCut.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTRTopActCut.lean#L18-L29

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCTheta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct.interp {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (W : Matrix (Fin N) (Fin N) ℂ)
    (hW : W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1) (p : ℂ → V) (a : ℕ → V)
    (ha : ∀ Y, p Y = ∑ j ∈ Finset.range N, Y ^ j • a j) (j : Fin N) :
    ∑ i : Fin N, W j i • p ((i : ℕ) : ℂ) = a j := by sorry
