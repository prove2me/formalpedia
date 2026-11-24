-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RestrictedDualKernel_cs_on
-- name    : Formalism.FourierDecayAlt.P.RestrictedDualKernel.cs_on
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:19:22.274025+00:00
-- url     : https://prove2.me/theorems/8f27105b-8abf-42db-977c-5140da2e30f1
-- title:
--   Restricted Dual Kernel: cs on
-- statement:
--   The Restricted Dual Kernel construction uses the cs on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictedDualKernel.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictedDualKernel.lean#L13-L20

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

theorem Formalism.FourierDecayAlt.P.RestrictedDualKernel.cs_on (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X : Submodule ℂ (Ix S → V)) (hP : IsPosOn ρ M X)
    {x y : Ix S → V} (hx : x ∈ X) (hy : y ∈ X) :
    ‖frm ρ M x y‖ ^ 2 ≤ (frm ρ M x x).re * (frm ρ M y y).re := by sorry
