-- Prove2me | Theorems.Thm_Formalism_H_dualEquiv_apply
-- name    : Formalism.H.dualEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:35.697939+00:00
-- url     : https://prove2.me/theorems/7a33fba6-1090-4e1d-9dc6-8b1a2dafc077
-- title:
--   H: dual Equiv apply
-- statement:
--   The H construction uses the dual Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/InnerDualVecBasis.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/InnerDualVecBasis.lean#L67-L68

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_InnerDualVecBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Complex
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Formalism.H.dualEquiv_apply (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    ((dualEquiv e m : dual (Submodule.span ℤ (Set.range e))) : V) = dualVec e m := by sorry

attribute [defeq] Formalism.H.dualEquiv_apply
