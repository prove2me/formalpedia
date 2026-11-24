-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RestrictedDualKernel_pos_mul
-- name    : Formalism.FourierDecayAlt.P.RestrictedDualKernel.pos_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:24.357195+00:00
-- url     : https://prove2.me/theorems/bada1f46-3064-4c74-ae07-92d337be43dc
-- title:
--   Restricted Dual Kernel: pos mul
-- statement:
--   The Restricted Dual Kernel construction uses the pos mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictedDualKernel.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictedDualKernel.lean#L22-L28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictedDualKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RestrictedDualKernel
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix ComplexOrder
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem Formalism.FourierDecayAlt.P.RestrictedDualKernel.pos_mul {c u : ℂ} (hc : 0 < c) (hu : 0 ≤ u.re ∧ u.im = 0) : 0 ≤ (c * u).re ∧ (c * u).im = 0 := by sorry
