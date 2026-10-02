-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_polyhedral_mconvex_operations
-- name    : DiscreteConvex.MConvexFunctionsD.polyhedral_mconvex_operations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:53:00.649983+00:00
-- url     : https://prove2.me/theorems/de02f803-d7e0-47a9-a329-3c8af5d1dc95
-- title:
--   Theorem 6.49 -- polyhedral_mconvex_operations
-- statement:
--   **Theorem 6.49** (p.162-163), operations (1)-(4). Let $f\in M[\mathbb R\to\mathbb R]$ be polyhedral M-convex. (1) $\lambda f$ is polyhedral M-convex for $\lambda>0$. (2) $f(a+\beta x)$ is polyhedral M-convex in $x$, for $a\in\mathbb R^V$, $\beta\ne 0$. (3) $f[-p]$ is polyhedral M-convex for $p\in\mathbb R^V$. (4) The separable perturbation $f(x)+\sum_v\phi_v(x(v))$ is polyhedral M-convex, for convex univariate $\phi_v$, provided its domain is nonempty.
--
--   **Formalization Note.** Parts (5)-(8) (real-interval restriction, restriction to $U$, aggregation, infimal convolution) are not restated here — the same scope decision as chunk `22-ch06b-mconvexfunctions`'s Theorem 6.13, see `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162-163, Theorem 6.49.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162-163, Theorem 6.49

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosScalarMul
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsConvexUniv
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SeparablePerturbR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.49 (p.181-182), operations (1)-(4); (5)-(8) are not restated here (see
`MODERATION_NOTES.md`, the same scope decision as chunk `22-ch06b-mconvexfunctions`'s Theorem
6.13). -/
theorem polyhedral_mconvex_operations (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f) :
    (∀ lam : ℝ, 0 < lam → MExchangeAxiomR (fun x => PosScalarMul lam (f x))) ∧
    (∀ (a : V → ℝ) (beta : ℝ), beta ≠ 0 → MExchangeAxiomR (fun x => f (fun v => a v + beta * x v))) ∧
    (∀ p : V → ℝ, MExchangeAxiomR (LinearWeightR f p)) ∧
    (∀ phi : V → ℝ → WithTop ℝ, (∀ v, IsConvexUniv (phi v)) →
      (DomR (SeparablePerturbR f phi)).Nonempty → MExchangeAxiomR (SeparablePerturbR f phi)) := by sorry

end DiscreteConvex.MConvexFunctionsD
