-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ProductIntervalFrames_rho_eq
-- name    : Formalism.FourierDecayAlt.P.ProductIntervalFrames.rho_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:33:08.473884+00:00
-- url     : https://prove2.me/theorems/f459b27e-126f-4cb7-b036-89c2ecf37f9a
-- title:
--   Product Interval Frames: rho eq
-- statement:
--   The Product Interval Frames construction uses the rho eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductIntervalFrames.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductIntervalFrames.lean#L27-L32

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductIntervalFrames
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_rho_eq

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

theorem Formalism.FourierDecayAlt.P.ProductIntervalFrames.rho_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (ρ : M.Ty (par n r T T' u)) (j : Fin n) :
    M.rho (par n r T T' u) ρ ((j : ℕ) + 1) = u ((j : ℕ) + 2) + 1 / 2 + (((ρ j : Fin _) : ℕ) : ℝ) := by sorry
