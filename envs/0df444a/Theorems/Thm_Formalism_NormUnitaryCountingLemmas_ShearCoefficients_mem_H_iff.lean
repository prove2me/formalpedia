-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_mem_H_iff
-- name    : Formalism.NormUnitaryCountingLemmas.ShearCoefficients.mem_H_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:38.880804+00:00
-- url     : https://prove2.me/theorems/1618eabf-2363-473b-acb8-54293c172210
-- title:
--   Shear Coefficients: mem H iff
-- statement:
--   The Shear Coefficients construction uses the mem H iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean#L13-L19

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.ShearCoefficients
variable {R : Type*} [CommRing R]

theorem Formalism.NormUnitaryCountingLemmas.ShearCoefficients.mem_H_iff {N n : ℕ} (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) R) :
    F ∈ H R ν ↔ F.IsWeightedHomogeneous (blockWt N n) ν ∧
      ∀ i j : Fin N, i < j → shear R i j F = Polynomial.C F := by sorry
