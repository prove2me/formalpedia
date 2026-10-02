-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_quasi_submodular_hierarchy
-- name    : DiscreteConvex.LConvexFunctionsD.quasi_submodular_hierarchy
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:04:08.139608+00:00
-- url     : https://prove2.me/theorems/85d7a9bc-add2-432f-8607-6eb65fcab27a
-- title:
--   Theorem 7.49 -- quasi_submodular_hierarchy
-- statement:
--   **Theorem 7.49** (p.199). For $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$: (1) the implication diagram (SBF[Z])$\Rightarrow$(SSQSB)$\Rightarrow$(QSB), (SSQSB)$\Rightarrow$(SSQSBw), (QSB)$\Rightarrow$(QSBw); (2) $g$ satisfies (SBF[Z]) iff $g[x]$ satisfies (QSBw) for every $x\in\mathbb R^V$.
--
--   **Not in this chunk's own `BRIEF.md` table** — found by direct reading, the L-side analogue of mission `25-ch06e-mconvexfunctions`'s own missed Theorem 6.68, whose proof of part (2) likewise combines two milestones of its own chunk (Theorems 7.51 and 7.52).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, Theorem 7.49.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, Theorem 7.49

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSB
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSB
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightPlus

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.49 (p.199). The quasi-submodularity hierarchy: the implication diagram relating
(SBF[Z]), (SSQSB), (QSB) and their weak variants, and the identification of (SBF[Z]) with (QSBw)
holding for every linear perturbation of `g`. -/
theorem quasi_submodular_hierarchy (g : (V → ℤ) → WithTop ℝ) :
    (SBF g → SSQSB g) ∧ (SSQSB g → QSB g) ∧
    (SSQSB g → SSQSBw g) ∧ (QSB g → QSBw g) ∧
    (SBF g ↔ ∀ x : V → ℝ, QSBw (LinearWeightPlus g x)) := by sorry

end DiscreteConvex.LConvexFunctionsD
