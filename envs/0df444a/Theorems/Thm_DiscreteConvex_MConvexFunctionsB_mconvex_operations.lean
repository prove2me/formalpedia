-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_mconvex_operations
-- name    : DiscreteConvex.MConvexFunctionsB.mconvex_operations
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:10:29.673746+00:00
-- url     : https://prove2.me/theorems/1dfb71d5-68ad-44eb-b074-afd632b5d6bf
-- title:
--   Theorem 6.13 -- mconvex_operations
-- statement:
--   **Theorem 6.13** (p.143), operations (1)-(6). Let $f$ be M-convex. (1) $\lambda f$ is M-convex for $\lambda>0$. (2) $f(a-x)$ and $f(a+x)$ are M-convex in $x$, for $a \in \mathbb Z^V$. (3) $f[p]$ is M-convex for every $p \in \mathbb R^V$. (4) The separable perturbation $f(x)+\sum_v \phi_v(x(v))$ is M-convex, for discrete convex univariate $\phi_v$, provided its domain is nonempty. (5) The restriction $f_{[a,b]}$ to an integer interval is M-convex provided its domain is nonempty. (6) The restriction $f_U$ to $U\subseteq V$ is M-convex provided its domain is nonempty.
--
--   **Formalization Note.** Parts (7) (aggregation) and (8) (integer infimal convolution) are proved in the book only later, via network transformation in Chapter 9 (Notes 9.29-9.30), and are not restated here — see `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Theorem 6.13.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Theorem 6.13

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_PosScalarMul
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_LinearWeight
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SeparablePerturb
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_IntervalRestrict
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_Restriction

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.143, Theorem 6.13, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Theorem 6.13 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.143). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_operations {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) :
    (∀ lam : ℝ, 0 < lam → MExchangeAxiom (fun x => PosScalarMul lam (f x))) ∧
    (∀ a : V → ℤ, MExchangeAxiom (fun x => f (fun v => a v - x v)) ∧
      MExchangeAxiom (fun x => f (fun v => a v + x v))) ∧
    (∀ p : V → ℝ, MExchangeAxiom (LinearWeight f p)) ∧
    (∀ phi : V → ℤ → WithTop ℝ, (∀ v, DiscreteConvexUnivariate (phi v)) →
      (DomZ (SeparablePerturb f phi)).Nonempty → MExchangeAxiom (SeparablePerturb f phi)) ∧
    (∀ a b : V → WithBot (WithTop ℤ), (DomZ (IntervalRestrict f a b)).Nonempty →
      MExchangeAxiom (IntervalRestrict f a b)) ∧
    (∀ U : Finset V, (DomZ (Restriction f U)).Nonempty → MExchangeAxiom (Restriction f U)) := by sorry

end DiscreteConvex.MConvexFunctionsB
