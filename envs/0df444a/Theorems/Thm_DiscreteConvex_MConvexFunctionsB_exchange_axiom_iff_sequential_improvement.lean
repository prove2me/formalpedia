-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_exchange_axiom_iff_sequential_improvement
-- name    : DiscreteConvex.MConvexFunctionsB.exchange_axiom_iff_sequential_improvement
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:12:10.38482+00:00
-- url     : https://prove2.me/theorems/19bd334e-87ff-42b9-b050-d7a4f986f924
-- title:
--   Theorem 6.24 -- exchange_axiom_iff_sequential_improvement
-- statement:
--   **Theorem 6.24** (p.147-148). GOAL. Let $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ have nonempty effective domain. (1) $f$ is M-convex if and only if $f$ satisfies (M-SI[Z]), Eq. (6.51): for every linear weighting $p$ and every pair $x,y \in \operatorname{dom} f$ with $f[p](x) > f[p](y)$, $f[p]$ has a strict single-exchange descent direction from $x$. (2) $f$ is M$^\natural$-convex if and only if $f$ satisfies the analogous (M$^\natural$-SI[Z]), Eq. (6.52).
--
--   This recasts the static exchange axiom as a dynamic, algorithmically meaningful local-search condition: M-convexity is exactly what guarantees a greedy single-exchange step always finds a strict improvement whenever one exists, under any linear reweighting of the objective.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.147-148, Theorem 6.24, Eq. (6.51)-(6.52).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.147-148, Theorem 6.24

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MSI
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNatSI
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.147-148, Theorem 6.24, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Theorem 6.24 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.147-148). See the item's
`natural_language_statement` for the full statement. -/
theorem exchange_axiom_iff_sequential_improvement {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hdom : (DomZ f).Nonempty) :
    (MExchangeAxiom f ↔ MSI f) ∧ (MNaturalConvex f ↔ MNatSI f) := by sorry

end DiscreteConvex.MConvexFunctionsB
