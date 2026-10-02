-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_polyhedral_lconvex_four_characterizations
-- name    : DiscreteConvex.LConvexFunctionsD.polyhedral_lconvex_four_characterizations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:06:16.616202+00:00
-- url     : https://prove2.me/theorems/379b7bf3-1a98-4bae-b4b0-fbe8b966513a
-- title:
--   Theorem 7.45 -- polyhedral_lconvex_four_characterizations
-- statement:
--   **Theorem 7.45** (p.197-198). GOAL. For a polyhedral convex function $g:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ with $\operatorname{dom}_{\mathbb R} g\ne\emptyset$, the following are equivalent: (a) $g\in L[\mathbb R\to\mathbb R]$; (b) $g'(p;\cdot)\in 0L[\mathbb R\to\mathbb R]$ for every $p\in\operatorname{dom}_{\mathbb R} g$; (c) $\partial_{\mathbb R} g(p)\in M_0[\mathbb R]$ for every $p\in\operatorname{dom}_{\mathbb R} g$; (d) $\arg\min g[-x]\in L_0[\mathbb R]$ for every $x\in\mathbb R^V$ with $\arg\min g[-x]$ nonempty.
--
--   **Not in this chunk's own `BRIEF.md` table** — found by direct reading; its label starts a text line but the extractor evidently missed it, the same failure pattern as mission `25-ch06e-mconvexfunctions`'s Theorem 6.68. Chosen as goal per "take the deepest result": it is the direct L-side mirror of mission `24-ch06d-mconvexfunctions`'s milestone Theorem 6.63, is proved from Theorem 7.43, Proposition 7.34, and Theorem 7.40 (all already formalized in this series), and is the sentence a reader would cite if asked what characterizes polyhedral L-convexity across every classical convex-analytic vocabulary at once.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.197-198, Theorem 7.45.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.197-198, Theorem 7.45

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMinR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_MConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DirDeriv
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubDifferentialR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.45 (p.197-198). GOAL. Four characterizations of polyhedral L-convexity: via the
exchange-style axioms, positively-homogeneous directional derivatives, M-convex subdifferentials,
and L-convex weighted-minimizer polyhedra. (c) and (d) are in the real classes `M⁰[R]` and
`L⁰[R]`, which are not integral: `g(p) = (1/2) max(p₁ - p₂, 0)` satisfies (a) with
subdifferential the segment from `(0,0)` to `(1/2,-1/2)` at `0`, and `g(p) = max(p₁ - p₂ - 1/2, 0)`
satisfies (a) with minimizer set `{p : p₁ - p₂ ≤ 1/2}`; neither is the convex hull of an integer
set. -/
theorem polyhedral_lconvex_four_characterizations (g : (V → ℝ) → WithTop ℝ)
    (hdom : (DomR g).Nonempty) :
    [SBFR g ∧ TRFR g,
     ∀ p ∈ DomR g, ZeroLR (fun d => DirDeriv g p d),
     ∀ p ∈ DomR g, MConvexPolyhedronR (SubDifferentialR g p),
     ∀ x : V → ℝ, (ArgMinR (LinearWeightR g (fun v => - x v))).Nonempty →
        LConvexPolyhedronR (ArgMinR (LinearWeightR g (fun v => - x v)))].TFAE := by sorry

end DiscreteConvex.LConvexFunctionsD
