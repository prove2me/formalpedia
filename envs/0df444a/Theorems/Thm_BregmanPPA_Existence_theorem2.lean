-- Prove2me | Theorems.Thm_BregmanPPA_Existence_theorem2
-- name    : BregmanPPA.Existence.theorem2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:44.057189+00:00
-- url     : https://prove2.me/theorems/bc5eb3df-65df-4c30-b448-2b1e54f225b4
-- title:
--   Theorem 2 [5] — trimonotone operators, in particular subdifferentials, have the L-property
-- statement:
--   Let $H$ be a finite-dimensional real inner product space. Then:
--
--   1. every trimonotone operator $R:H\to2^H$ has the L-property;
--   2. in particular, for every proper convex $f:H\to(-\infty,+\infty]$, the subdifferential map $\partial f$ has the L-property.
--
--   That is, for such $R$ and all $u\in\operatorname{dom}R$, $v\in\operatorname{im}R$,
--   $$
--   \inf\{\langle x-u,\,y-v\rangle : y\in Rx\}>-\infty .
--   $$
--
--   This is the result of Brézis and Haraux that makes their range theorem (Theorem 3) applicable to the operator $\nabla h$ of a Bregman function in the proof of Theorem 4.
--
--   **Formalization Note** The paper's parenthetical remark that subdifferential maps are cyclically monotone [26] is the reason for the second clause; the second clause is stated separately for proper convex $f$ encoded as an `EReal`-valued function, so that it can be used without first proving cyclic monotonicity. Lower semicontinuity is not required for this claim.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 208, Theorem 2 (citing Brézis–Haraux [5])

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_BregmanPPA_Existence_Operators
import Definitions.Def_BregmanPPA_Existence_LProperty

open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR InertialFB.IFB

namespace BregmanPPA.Existence

/-- Theorem 2 [5] (p. 208): every trimonotone operator has the L-property; in particular the
subdifferential map of a proper convex function has it. -/
theorem theorem2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] :
    (∀ R : H → Set H, IsTrimonotone R → HasLProperty R) ∧
        (∀ f : H → EReal, IsProperFn f → IsConvexFn f →
      HasLProperty (BregmanPPA.Convergence.subdiffOp f)) := by sorry

end BregmanPPA.Existence
