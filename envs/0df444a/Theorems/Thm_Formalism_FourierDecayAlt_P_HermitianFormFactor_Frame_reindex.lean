-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_reindex
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame.reindex
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:58:28.679005+00:00
-- url     : https://prove2.me/theorems/531e3b49-dc7a-4900-b860-26e68014da83
-- title:
--   Frame: reindex
-- statement:
--   The Frame construction uses the reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L350-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L350-L369

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
open Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame.reindex {P' Q' : Type} [Fintype P'] [DecidableEq P'] [Fintype Q'] [DecidableEq Q']
    (F : Frame H Ep Em) (eP : P' ≃ P) (eQ : Q' ≃ Q) :
    Frame H (Ep.submatrix id eP) (Em.submatrix id eQ) := by sorry
