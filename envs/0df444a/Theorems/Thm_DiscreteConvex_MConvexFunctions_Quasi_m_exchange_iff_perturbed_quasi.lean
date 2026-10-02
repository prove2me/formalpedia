-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctions_Quasi_m_exchange_iff_perturbed_quasi
-- name    : DiscreteConvex.MConvexFunctions.Quasi.m_exchange_iff_perturbed_quasi
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:03:16.326507+00:00
-- url     : https://prove2.me/theorems/bac56b7a-682d-4229-97a1-860c76367ab9
-- title:
--   Theorem 6.68(2) -- M-convexity equals quasi M-convexity under every perturbation
-- statement:
--   **Theorem 6.68(2)** (p.171). A function $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ satisfies the M-convex exchange axiom (M-EXC[Z]) if and only if every linear perturbation $f[p]$ satisfies the weak quasi M-convexity condition (QMw). This shows (QMw) is much weaker than (M-EXC[Z]) pointwise (a single quasi-convex-looking function need not be M-convex at all), yet the two conditions coincide once (QMw) is required to hold simultaneously for *every* linear perturbation of $f$ — precisely quantifying how much weaker the quasi-convexity conditions this mission builds on really are.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, Theorem 6.68, part (2) only; part (1), an implication chain among six exchange/quasi-convexity axioms not otherwise needed by this mission's other items, is not drafted.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, Theorem 6.68(2)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_PerturbedM

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Theorem 6.68(2) (Murota, *Discrete Convex Analysis*, SIAM 2003, p.171). A function
`f : Zⱽ → R ∪ {+∞}` satisfies the M-convex exchange axiom (M-EXC[Z]) if and only if every
linear perturbation `f[p]` satisfies the weak quasi M-convexity condition (QMw). This shows
(QMw) is much weaker than (M-EXC[Z]) pointwise, yet the two conditions collapse to the same
class once (QMw) is required to hold simultaneously for every perturbation. -/
theorem m_exchange_iff_perturbed_quasi {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) :
    MExchangeAxiom f ↔ ∀ p : V → ℝ, QMw (PerturbedM f p) := by sorry

end DiscreteConvex.MConvexFunctions.Quasi
