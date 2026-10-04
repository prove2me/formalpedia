-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_univariate_convex_examples
-- name    : DiscreteConvex.MConvexFunctionsB.univariate_convex_examples
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:11:40.824506+00:00
-- url     : https://prove2.me/theorems/39dd7ba1-4e18-4477-b338-d0f1079ae085
-- title:
--   Proposition 6.9 -- univariate_convex_examples
-- statement:
--   **Proposition 6.9** (p.140), plus its "moreover" clause. Let $\psi$ be a discrete convex univariate function. (1) $\psi$ is M$^\natural$-convex. (2) The conservation-law lift $f(x)=\psi(x(1))$ if $x(1)+x(2)=0$, else $+\infty$, is M-convex. Moreover, every quasi-separable convex function $f(x)=f_0(\sum_i x(i))+\sum_i f_i(x(i))$ (Eq. (6.32)) built from discrete convex univariate $f_0,f_1,\ldots$ is M$^\natural$-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, Proposition 6.9, Eq. (6.32).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.140, Proposition 6.9

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_UnivToFunc
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ConservationLift
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuasiSeparable

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.140, Proposition 6.9, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.9 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.140). See the item's
`natural_language_statement` for the full statement. -/
theorem univariate_convex_examples (psi : ℤ → WithTop ℝ) (hpsi : DiscreteConvexUnivariate psi) :
    MNaturalConvex (UnivToFunc psi) ∧
    MExchangeAxiom (ConservationLift psi) ∧
    (∀ {W : Type*} [Fintype W] [DecidableEq W] (f0 : ℤ → WithTop ℝ) (fi : W → ℤ → WithTop ℝ),
      DiscreteConvexUnivariate f0 → (∀ v, DiscreteConvexUnivariate (fi v)) →
      MNaturalConvex (QuasiSeparable f0 fi)) := by sorry

end DiscreteConvex.MConvexFunctionsB
