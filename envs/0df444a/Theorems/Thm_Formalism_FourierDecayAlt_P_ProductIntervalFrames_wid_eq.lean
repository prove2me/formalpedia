-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ProductIntervalFrames_wid_eq
-- name    : Formalism.FourierDecayAlt.P.ProductIntervalFrames.wid_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:14:53.770826+00:00
-- url     : https://prove2.me/theorems/4616b1f8-aa62-5d67-9900-f55eab66b5a8
-- title:
--   Product Interval Frames: wid eq
-- statement:
--   The Product Interval Frames construction uses the wid eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductIntervalFrames.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductIntervalFrames.lean#L34-L48

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductIntervalFrames
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_wid_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_wid_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

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

theorem Formalism.FourierDecayAlt.P.ProductIntervalFrames.wid_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (L : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc) (j : Fin n) :
    (((par n r T T' u).wid ((j : ℕ) + 1) : ℕ) : ℤ) = L j.castSucc - L j.succ - 1 := by sorry
