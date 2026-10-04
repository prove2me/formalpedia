-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_quasi_mconvex_hierarchy
-- name    : DiscreteConvex.MConvexFunctionsE.quasi_mconvex_hierarchy
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:10:08.581224+00:00
-- url     : https://prove2.me/theorems/1c3860ea-601b-4913-8dd1-20966b0bff9f
-- title:
--   Theorem 6.68 -- quasi_mconvex_hierarchy
-- statement:
--   **Theorem 6.68** (p.171). GOAL. For $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$: (1) the implication diagram (M-EXC[Z])$\Rightarrow$(SSQM)$\Rightarrow$(QM), (M-EXCw[Z])$\Rightarrow$(SSQMw)$\Rightarrow$(QMw), (M-EXC[Z])$\Leftrightarrow$(M-EXCw[Z]), (SSQM)$\Rightarrow$(SSQMw), (QM)$\Rightarrow$(QMw); (2) $f$ satisfies (M-EXC[Z]) iff $f[p]$ satisfies (QMw) for every $p\in\mathbb R^V$.
--
--   This is the capstone of section 6.14: it is proved by combining Theorem 6.72 and Theorem 6.74 (both milestones of this mission), and identifies M-convexity exactly with the property that every linear perturbation of $f$ is quasi M-convex in the weak sense — the discrete exchange axiom is, in a precise quantifier-free sense, the same as quasi-convexity of every perturbation.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, Theorem 6.68.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, Theorem 6.68

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiomW
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QM
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQM
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeight

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.68 (p.171). GOAL. The quasi M-convexity hierarchy: the implication diagram
relating (M-EXC[Z]), (SSQM), (QM) and their weak variants, and the identification of
(M-EXC[Z]) with (QMw) holding for every linear perturbation of `f`. -/
theorem quasi_mconvex_hierarchy (f : (V → ℤ) → WithTop ℝ) :
    (MExchangeAxiom f → SSQM f) ∧
    (SSQM f → QM f) ∧
    (MExchangeAxiomW f → SSQMw f) ∧
    (SSQMw f → QMw f) ∧
    (MExchangeAxiom f ↔ MExchangeAxiomW f) ∧
    (SSQM f → SSQMw f) ∧
    (QM f → QMw f) ∧
    (MExchangeAxiom f ↔ ∀ p : V → ℝ, QMw (LinearWeight f p)) := by sorry

end DiscreteConvex.MConvexFunctionsE
