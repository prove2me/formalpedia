-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_taylorMv_coeff
-- name    : Formalism.L2.Th1.H.taylorMv_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:50.474482+00:00
-- url     : https://prove2.me/theorems/c9ca5dab-c765-461e-8a35-fd81da6dc89c
-- title:
--   H: taylor Mv coeff
-- statement:
--   The H construction uses the taylor Mv coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/IteratedDerivLine.lean#L94-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/IteratedDerivLine.lean#L94-L106

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.taylorMv_coeff {n : Type*} [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ) (k : ℕ) (ν : n →₀ ℕ)
    (h : ν.degree = k) :
    MvPowerSeries.coeff ν (taylorMv F) = ((k.factorial : ℕ) : ℂ)⁻¹ *
      ∑ f : Fin k → n with cntVec f = ν, iteratedFDeriv ℂ k F 0 fun j => Pi.single (f j) (1 : ℂ) := by sorry
