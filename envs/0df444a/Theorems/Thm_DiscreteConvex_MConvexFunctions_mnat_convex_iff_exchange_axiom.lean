-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctions_mnat_convex_iff_exchange_axiom
-- name    : DiscreteConvex.MConvexFunctions.mnat_convex_iff_exchange_axiom
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:59:24.648155+00:00
-- url     : https://prove2.me/theorems/df80d981-f7f1-44a7-abba-072b14412a81
-- title:
--   Theorem 6.2 -- M-natural-convexity equals the direct exchange axiom
-- statement:
--   **Theorem 6.2** (p.135). For $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ with $\operatorname{dom} f \ne \emptyset$, $f$ is M$^\natural$-convex if and only if $f$ satisfies the direct exchange axiom (M$^\natural$-EXC[Z]). This is the chapter's central definitional equivalence: M$^\natural$-convexity is *defined* via a lift to an extended ground set, and this theorem shows it agrees with a direct, more usable exchange condition.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.135, Theorem 6.2.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.135, Theorem 6.2

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNatExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ

namespace DiscreteConvex.MConvexFunctions

/-- Theorem 6.2 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.135). For a function
`f : Zⱽ → R ∪ {+∞}` with `dom f ≠ ∅`, `f` is M♮-convex if and only if `f` satisfies the direct
exchange axiom (M♮-EXC[Z]). -/
theorem mnat_convex_iff_exchange_axiom {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : (DomZ f).Nonempty) :
    MNaturalConvex f ↔ MNatExchangeAxiom f := by sorry

end DiscreteConvex.MConvexFunctions
