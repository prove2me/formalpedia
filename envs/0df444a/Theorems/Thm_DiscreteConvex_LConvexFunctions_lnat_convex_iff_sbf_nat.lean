-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctions_lnat_convex_iff_sbf_nat
-- name    : DiscreteConvex.LConvexFunctions.lnat_convex_iff_sbf_nat
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:15:14.013974+00:00
-- url     : https://prove2.me/theorems/31a155c3-13c7-4e08-b006-3daf4896288e
-- title:
--   Theorem 7.1 -- L-natural-convexity equals the direct translation-submodularity axiom
-- statement:
--   **Theorem 7.1** (p.178). For $g : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ with $\operatorname{dom} g \ne \emptyset$, $g$ is L$^\natural$-convex if and only if $g$ satisfies the direct translation-submodularity axiom (SBF$^\natural$[Z]). The direct analogue, for L-convexity, of chunk 06's Theorem 6.2 for M$^\natural$-convexity.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Theorem 7.1.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, Theorem 7.1

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBFNat
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ

namespace DiscreteConvex.LConvexFunctions

/-- Theorem 7.1 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.178). For a function
`g : Zⱽ → R ∪ {+∞}` with `dom g ≠ ∅`, `g` is L♮-convex if and only if `g` satisfies the direct
translation-submodularity axiom (SBF♮[Z]). -/
theorem lnat_convex_iff_sbf_nat {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) (hg : (DomZ g).Nonempty) :
    LNaturalConvex g ↔ SBFNat g := by sorry

end DiscreteConvex.LConvexFunctions
