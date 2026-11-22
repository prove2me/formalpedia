-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_lamLin_mk_eq
-- name    : Formalism.FourierDecayAlt.P.A5x4.lamLin_mk_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:48:58.804842+00:00
-- url     : https://prove2.me/theorems/a089fca3-bc75-4be1-b2b0-3f1fbbb4f45f
-- title:
--   A5x4: lam Lin mk eq
-- statement:
--   The A5x4 construction uses the lam Lin mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L338-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelQuotientFinite.lean#L338-L355

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x4.lamLin_mk_eq {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) {v v' : Fin n → R}
    (h : (Submodule.Quotient.mk v : coker R Z) = Submodule.Quotient.mk v') :
    lamLin R Z v = lamLin R Z v' := by sorry
