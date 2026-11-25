-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_Ts_mem
-- name    : Formalism.FourierDecayAlt.P5.Ts_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:56:38.897541+00:00
-- url     : https://prove2.me/theorems/dde27abd-5327-4e69-86f3-43ae33829df3
-- title:
--   P5: Ts mem
-- statement:
--   The P5 construction uses the Ts mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L270-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L270-L278

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P5.Ts_mem {T : Subalgebra ℂ (Pr V)} (σ : Site (Pr V)) (Y : ℂ) (hp : σ.p ∈ T) (hc : σ.c ∈ T)
    (hci : σ.ci ∈ T) (a b : Fin 2) : Ts σ Y a b ∈ T := by sorry
