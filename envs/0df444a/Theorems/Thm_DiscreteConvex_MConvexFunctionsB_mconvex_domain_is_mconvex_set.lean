-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_mconvex_domain_is_mconvex_set
-- name    : DiscreteConvex.MConvexFunctionsB.mconvex_domain_is_mconvex_set
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:09:53.436302+00:00
-- url     : https://prove2.me/theorems/85d7bb66-34f6-4ef3-83e7-aaca4299c637
-- title:
--   Proposition 6.1 -- mconvex_domain_is_mconvex_set
-- statement:
--   **Proposition 6.1** (p.134). The effective domain of an M-convex function is an M-convex set. Therefore, it lies on a hyperplane $\{x \in \mathbb R^V : x(V)=r\}$ for some integer $r$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Proposition 6.1.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Proposition 6.1

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134, Proposition 6.1, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.1 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.134). See the item's
`natural_language_statement` for the full statement. -/
theorem mconvex_domain_is_mconvex_set {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) :
    ExchangeAxiomB (DomZ f) ∧ ∃ r : ℤ, ∀ x ∈ DomZ f, ∑ v, x v = r := by sorry

end DiscreteConvex.MConvexFunctionsB
