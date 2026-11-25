-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ProductIntervalFrames_isInternal_comp
-- name    : Formalism.FourierDecayAlt.P.ProductIntervalFrames.isInternal_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:06:05.642084+00:00
-- url     : https://prove2.me/theorems/4dee1f17-9060-5bbc-91d5-9cef4ea80378
-- title:
--   Product Interval Frames: is Internal comp
-- statement:
--   The Product Interval Frames construction uses the is Internal comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductIntervalFrames.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductIntervalFrames.lean#L12-L16

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductIntervalFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductIntervalFrames
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.ProductIntervalFrames.isInternal_comp {ι κ W : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup W] [Module ℂ W]
    (Φ : ι → κ) (hΦ : Function.Bijective Φ) (S : κ → Submodule ℂ W) (h : DirectSum.IsInternal S) :
    DirectSum.IsInternal (fun i => S (Φ i)) := by sorry
