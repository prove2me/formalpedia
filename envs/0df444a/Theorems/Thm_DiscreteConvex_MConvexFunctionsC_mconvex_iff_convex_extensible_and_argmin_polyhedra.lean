-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mconvex_iff_convex_extensible_and_argmin_polyhedra
-- name    : DiscreteConvex.MConvexFunctionsC.mconvex_iff_convex_extensible_and_argmin_polyhedra
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:43:54.041714+00:00
-- url     : https://prove2.me/theorems/948369b5-09dd-46f5-ad17-3c2726dc37b4
-- title:
--   Theorem 6.43 -- mconvex_iff_convex_extensible_and_argmin_polyhedra
-- statement:
--   **Theorem 6.43** (p.159). GOAL. Let $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ with $\operatorname{dom} f \ne \emptyset$ and convex closure $\bar f$. (1) $f$ is M-convex iff (i) $f$ is convex extensible and (ii) for every $p\in\mathbb R^V$, $\arg\min \bar f[-p]$ is an M-convex polyhedron whenever nonempty. (2) The M$^\natural$ analogue with M$^\natural$-convex polyhedra.
--
--   This characterizes the convex extension of an M-convex function entirely in terms of the polyhedral structure of its weighted minimizer sets, the bridge between the discrete exchange axiom and the continuous theory of chapter 8's separation and conjugacy results.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.159, Theorem 6.43.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.159, Theorem 6.43

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MConvexPolyhedron
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatConvexPolyhedron
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CCWeight

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.43 (p.159). GOAL. -/
theorem mconvex_iff_convex_extensible_and_argmin_polyhedra (f : (V → ℤ) → WithTop ℝ)
    (hdom : (DomZ f).Nonempty) :
    (MExchangeAxiom f ↔
      (ConvexExtensible f ∧ ∀ p : V → ℝ, (ArgMinOn (CCWeight f p)).Nonempty →
        MConvexPolyhedron (ArgMinOn (CCWeight f p)))) ∧
    (MNaturalConvex f ↔
      (ConvexExtensible f ∧ ∀ p : V → ℝ, (ArgMinOn (CCWeight f p)).Nonempty →
        MNatConvexPolyhedron (ArgMinOn (CCWeight f p)))) := by sorry

end DiscreteConvex.MConvexFunctionsC
