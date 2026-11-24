-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Ppos_eq
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.Ppos_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:13:45.221967+00:00
-- url     : https://prove2.me/theorems/bebea37a-294c-4ed0-8217-e44896c21d0e
-- title:
--   Hermitian Form Factor: Ppos eq
-- statement:
--   The Hermitian Form Factor construction uses the Ppos eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L193-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L193-L200

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.Ppos_eq {k r : ℕ} {Ep : Matrix (Fin (2 * r + k + 1)) P ℂ} {Em : Matrix (Fin (2 * r + k + 1)) Q ℂ}
    (F : Frame (Hpk k r) Ep Em) : Ppos k r = Ep * Epᴴ := by sorry
