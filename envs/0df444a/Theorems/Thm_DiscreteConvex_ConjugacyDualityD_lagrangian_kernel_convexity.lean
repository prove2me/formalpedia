-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_lagrangian_kernel_convexity
-- name    : DiscreteConvex.ConjugacyDualityD.lagrangian_kernel_convexity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:03:08.498093+00:00
-- url     : https://prove2.me/theorems/f6c3868b-40f6-43b6-bbef-ecb717c2054c
-- title:
--   Theorem 8.57 -- lagrangian_kernel_convexity
-- statement:
--   **Theorem 8.57** (p.240). Convexity/concavity of the Lagrangian kernel in each argument: (1) for fixed $x$, $K_0(x,\cdot)$ is the negation of an L-convex function (or identically $+\infty$); (2) for fixed $x$, $K_r(x,\cdot)$ is the negation of an L2-convex function (or identically $+\infty$); (3) if $c$ is M-convex, then for fixed $y$, $K_0(\cdot,y)$ is (embeds) an M-convex function, or is identically $+\infty$, or is identically $-\infty$; (4) likewise $K_r(\cdot,y)$ embeds an M2-convex function, or is identically $+\infty$, or identically $-\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240, Theorem 8.57.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240, Theorem 8.57

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsEmbedOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsNegOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.57 (p.240). Convexity/concavity of the Lagrangian kernel `Kr` in each of its
arguments. The book's second case in (3) and (4) is "takes only the values `+∞` and `-∞`", with
the two allowed to be mixed over `x`, not "constantly `+∞` or constantly `-∞`": with `B` the line
`{x₁ + x₂ = 0}`, `c` the indicator of `0` and `y = (1, 0)`, `K₀(0, y) = -∞` while `K₀(x, y) = +∞`
for every `x ≠ 0`. -/
theorem lagrangian_kernel_convexity (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hB : ExchangeAxiomB B) (hr : MExchangeAxiom r) :
    (∀ x, IsNegOf (fun h => SBF h ∧ TRF h) (fun y => KR c (fun _ => (0 : WithTop ℝ)) B x y) ∨
      ∀ y, KR c (fun _ => (0 : WithTop ℝ)) B x y = ⊤) ∧
    (∀ x, IsNegOf L2Convex (fun y => KR c r B x y) ∨ ∀ y, KR c r B x y = ⊤) ∧
    (MExchangeAxiom c →
      ∀ y, IsEmbedOf MExchangeAxiom (fun x => KR c (fun _ => (0 : WithTop ℝ)) B x y) ∨
        (∀ x, KR c (fun _ => (0 : WithTop ℝ)) B x y = ⊤ ∨
          KR c (fun _ => (0 : WithTop ℝ)) B x y = ⊥)) ∧
    (MExchangeAxiom c →
      ∀ y, IsEmbedOf M2Convex (fun x => KR c r B x y) ∨
        (∀ x, KR c r B x y = ⊤ ∨ KR c r B x y = ⊥)) := by sorry

end DiscreteConvex.ConjugacyDualityD
