-- Prove2me | Theorems.Thm_Formalism_H_covolDual_det_mul
-- name    : Formalism.H.covolDual_det_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:13.787473+00:00
-- url     : https://prove2.me/theorems/e27b8877-ad12-43db-8567-64f141cc6556
-- title:
--   H: covol Dual det mul
-- statement:
--   The H construction uses the covol Dual det mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/CovolumeDual.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/CovolumeDual.lean#L16-L39

import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

theorem Formalism.H.covolDual_det_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : OrthonormalBasis ι ℝ V) (e : Module.Basis ι ℝ V) :
    o.toBasis.det (LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e) * o.toBasis.det e = 1 := by sorry
