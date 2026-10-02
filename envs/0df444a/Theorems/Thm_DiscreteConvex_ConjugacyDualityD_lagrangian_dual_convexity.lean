-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_lagrangian_dual_convexity
-- name    : DiscreteConvex.ConjugacyDualityD.lagrangian_dual_convexity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:03:49.707885+00:00
-- url     : https://prove2.me/theorems/b8f0a7db-b9dc-4075-930d-abd06d8feaba
-- title:
--   Theorem 8.58 -- lagrangian_dual_convexity
-- statement:
--   **Theorem 8.58** (p.240). For an M-convex program, the dual objective and optimal-value functions are well behaved: (1) $g_0$ is the negation of an L-convex function, or identically $-\infty$; (2) $g_r$ is the negation of an L2-convex function, or identically $\pm\infty$; (3) $\varphi_0$ embeds an M-convex function, or is identically $+\infty$, or identically $-\infty$; (4) $\varphi_r$ embeds an M2-convex function, or is identically $\pm\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240, Theorem 8.58.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.240, Theorem 8.58

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_SBF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_TRF
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsEmbedOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsNegOf
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiR
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRSmall

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.58 (p.240). For an M-convex program, the dual objective and optimal-value
functions are themselves well behaved: L-(resp. L2-)concave and M-(resp. M2-)convex. As in
Theorem 8.57, the book's second case in (3) and (4) allows `+∞` and `-∞` to be mixed over `u`:
with `B` the line `{x₁ + x₂ = 0}` and `c(x) = x₁` on `B`, `φ₀` is `-∞` on `B` and `+∞` off it. -/
theorem lagrangian_dual_convexity (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ))
    (hB : ExchangeAxiomB B) (hc : MExchangeAxiom c) (hr : MExchangeAxiom r) :
    (IsNegOf (fun h => SBF h ∧ TRF h) (GRSmall c (fun _ => (0 : WithTop ℝ)) B) ∨
      ∀ y, GRSmall c (fun _ => (0 : WithTop ℝ)) B y = ⊥) ∧
    (IsNegOf L2Convex (GRSmall c r B) ∨ (∀ y, GRSmall c r B y = ⊥) ∨
      (∀ y, GRSmall c r B y = ⊤)) ∧
    (IsEmbedOf MExchangeAxiom (PhiR c (fun _ => (0 : WithTop ℝ)) B) ∨
      (∀ u, PhiR c (fun _ => (0 : WithTop ℝ)) B u = ⊤ ∨
        PhiR c (fun _ => (0 : WithTop ℝ)) B u = ⊥)) ∧
    (IsEmbedOf M2Convex (PhiR c r B) ∨ (∀ u, PhiR c r B u = ⊤ ∨ PhiR c r B u = ⊥)) := by sorry

end DiscreteConvex.ConjugacyDualityD
