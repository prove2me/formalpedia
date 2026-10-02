-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_mconvex_four_characterizations
-- name    : DiscreteConvex.MConvexFunctionsE.mconvex_four_characterizations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:10:29.309839+00:00
-- url     : https://prove2.me/theorems/0a8c7a3b-8854-43e8-9ce0-43e9a6030c35
-- title:
--   Theorem 6.63 -- mconvex_four_characterizations
-- statement:
--   **Theorem 6.63** (p.167-168). For a polyhedral convex function $f:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ with $\operatorname{dom}_{\mathbb R} f\ne\emptyset$, the following are equivalent: (a) $f\in M[\mathbb R\to\mathbb R]$; (b) $f'(x;\cdot)\in 0M[\mathbb R\to\mathbb R]$ for every $x\in\operatorname{dom}_{\mathbb R} f$; (c) $\partial_{\mathbb R} f(x)\in L_0[\mathbb R]$ for every $x\in\operatorname{dom}_{\mathbb R} f$; (d) $\arg\min f[-p]\in M_0[\mathbb R]$ for every $p\in\mathbb R^V$ with $\arg\min f[-p]$ nonempty.
--
--   **Formalization Note.** The book states (d) for every $p$ with $\inf f[-p] > -\infty$; since the codomain `WithTop ℝ` has no distinguished $-\infty$ element, this hypothesis is replaced by the equivalent, established convention `(ArgMinOn ...).Nonempty` (matching mission `23-ch06c-mconvexfunctions`'s Theorem 6.43). $M_0[\mathbb R]$ is realized via the indicator-function device the book itself uses to relate quasi M-convex sets to functions (section 6.14) — see `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.167-168, Theorem 6.63.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.167-168, Theorem 6.63

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeightR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DirDeriv
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_ZeroMR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsL0R
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SubDifferentialR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsMZeroR

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.63 (p.167-168). Four characterizations of **polyhedral** M-convexity: the page's
class is the polyhedral convex functions with nonempty domain, and the bare exchange axiom is not
enough. `f(x) = -√(1-x₁²)` on the line `x₁ + x₂ = 0` (`|x₁| ≤ 1`) satisfies (a), but at
`x = (-1,1)` its subdifferential is empty while the admissible potential set of a triangle
inequality distance is not, so (c) fails. -/
theorem mconvex_four_characterizations (f : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex f) (hdom : (DomR f).Nonempty) :
    [MExchangeAxiomR f,
     ∀ x ∈ DomR f, ZeroMR (fun d => DirDeriv f x d),
     ∀ x ∈ DomR f, IsL0R (SubDifferentialR f x),
     ∀ p : V → ℝ, (ArgMinOn (LinearWeightR f (fun v => -p v))).Nonempty →
        IsMZeroR (ArgMinOn (LinearWeightR f (fun v => -p v)))].TFAE := by sorry

end DiscreteConvex.MConvexFunctionsE
