-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_multilinear_diag
-- name    : Formalism.L2.Th1.H.multilinear_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:23.163188+00:00
-- url     : https://prove2.me/theorems/21d4a488-4de1-435c-8a6d-eff5dda51106
-- title:
--   H: multilinear diag
-- statement:
--   The H construction uses the multilinear diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/IteratedDerivLine.lean#L108-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/IteratedDerivLine.lean#L108-L118

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

theorem Formalism.L2.Th1.H.multilinear_diag {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
    (D : ContinuousMultilinearMap ℂ (fun _ : Fin k => n → ℂ) ℂ) (v : n → ℂ) :
    D (fun _ => v) = ∑ f : Fin k → n, (∏ j, v (f j)) * D fun j => Pi.single (f j) (1 : ℂ) := by sorry
