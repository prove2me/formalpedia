-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_general_duality_relations
-- name    : DiscreteConvex.ConjugacyDualityD.general_duality_relations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T02:00:53.095514+00:00
-- url     : https://prove2.me/theorems/2f7fafd3-6de6-44e6-9208-3cd8c5fdea73
-- title:
--   Theorem 8.53 -- general_duality_relations
-- statement:
--   **Theorem 8.53**, parts (1),(2),(4) (p.237). For an arbitrary perturbation function $F:\mathbb Z^V\times\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ with optimal-value function $\varphi(u)=\inf_x F(x,u)$ and dual objective $g(y)=\inf_x K(x,y)$: (1) $g(y) = -\varphi^{\bullet}(-y)$ (the dual objective is the negated convex conjugate of $\varphi$ at $-y$); (2) $\sup_y g(y) = \varphi^{\bullet\bullet}(0)$ (weak duality via biconjugacy); (4) $\varphi(0)=\sup_y g(y)$ if and only if $\varphi(0)=\varphi^{\bullet\bullet}(0)$ (strong duality holds iff $\varphi$ is biconjugate-exact at $0$).
--
--   **Scope reduction.** This chunk omits parts (3), (5), (6) of Theorem 8.53, which characterize the dual-optimal set $\operatorname{argmax} g$ via the subdifferential of $\varphi$ at $0$ under the book's own hypothesis (8.55) (a biconjugacy assumption established later, specifically for the M-convex case, in Theorem 8.59 of this same chunk). Parts (1),(2),(4) are the purely algebraic identities that hold unconditionally for any $F$; see `HARD.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237, Theorem 8.53.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237, Theorem 8.53

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_PhiGen
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GGen

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.53 (p.237), parts (1),(2),(4). General identities relating the optimal-value
function, the Lagrangian dual objective, and biconjugacy, for an arbitrary perturbation `F`. -/
theorem general_duality_relations (F : (V → ℤ) → (V → ℤ) → WithTop ℝ) :
    (∀ y : V → ℤ, GGen F y = -(ConvexConjE (PhiGen F) (fun v => -y v))) ∧
    (sSup {t : EReal | ∃ y, t = GGen F y} = ConvexConjE (ConvexConjE (PhiGen F)) 0) ∧
    (PhiGen F 0 = sSup {t : EReal | ∃ y, t = GGen F y} ↔
      PhiGen F 0 = ConvexConjE (ConvexConjE (PhiGen F)) 0) := by sorry

end DiscreteConvex.ConjugacyDualityD
