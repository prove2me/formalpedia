-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_intK_eq_sum
-- name    : Formalism.FourierDecayAlt.P.HessianScalingIntegrals.intK_eq_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:59.119432+00:00
-- url     : https://prove2.me/theorems/9276fb1c-eba8-4351-b0bf-9fed88d66e66
-- title:
--   Hessian Scaling Integrals: int K eq sum
-- statement:
--   The Hessian Scaling Integrals construction uses the int K eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L26-L35

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.HessianScalingIntegrals.intK_eq_sum (R : Subring K) (Λ L : AddSubgroup K) (d : ℕ)
    (hfin : {y : Fin d → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ L}.Finite)
    (g : (Fin d → K) → ℂ) (hg : ∀ x, g x ≠ 0 → ∀ i, x i ∈ L) :
    intK R Λ d g = (volL R Λ : ℂ) ^ d * ∑ y ∈ hfin.toFinset, g (fun i => Quotient.out (y i)) := by sorry
