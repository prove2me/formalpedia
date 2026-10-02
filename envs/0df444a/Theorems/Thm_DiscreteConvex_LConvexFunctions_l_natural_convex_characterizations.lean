-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctions_l_natural_convex_characterizations
-- name    : DiscreteConvex.LConvexFunctions.l_natural_convex_characterizations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:15:09.90905+00:00
-- url     : https://prove2.me/theorems/1099c352-d784-4e84-a86f-8403736a8270
-- title:
--   Theorem 7.7 -- discrete midpoint convexity characterizes L-natural-convexity
-- statement:
--   **Theorem 7.7** (p.180). For $g : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ with $\operatorname{dom} g \ne \emptyset$, the translation-submodularity axiom (SBF$^\natural$[Z]), the approach property (L$^\natural$-APR[Z]), and discrete midpoint convexity are all equivalent, and each is a necessary and sufficient condition for $g$ to be L$^\natural$-convex. Discrete midpoint convexity has no counterpart in the M-convex theory of chunk 06 — it is a distinctively L-convex phenomenon, and this theorem shows it is exactly as strong as the axiomatic definition.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Theorem 7.7.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Theorem 7.7

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBFNat
import Definitions.Def_DiscreteConvex_LConvexFunctions_LAPR
import Definitions.Def_DiscreteConvex_LConvexFunctions_DiscreteMidpointConvexity
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ

namespace DiscreteConvex.LConvexFunctions

/-- Theorem 7.7 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.180). For a function
`g : Zⱽ → R ∪ {+∞}` with `dom g ≠ ∅`, the translation-submodularity axiom (SBF♮[Z]), the
approach property (L♮-APR[Z]), and discrete midpoint convexity are all equivalent, and each is
a necessary and sufficient condition for `g` to be L♮-convex. -/
theorem l_natural_convex_characterizations {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) (hg : (DomZ g).Nonempty) :
    [SBFNat g, LAPR g, DiscreteMidpointConvexity g].TFAE := by sorry

end DiscreteConvex.LConvexFunctions
