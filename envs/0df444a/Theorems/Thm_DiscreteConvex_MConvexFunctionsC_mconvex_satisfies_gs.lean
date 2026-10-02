-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_mconvex_satisfies_gs
-- name    : DiscreteConvex.MConvexFunctionsC.mconvex_satisfies_gs
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:30:24.550045+00:00
-- url     : https://prove2.me/theorems/6bd1b0b2-bbf5-409d-b4fa-e21f1f054884
-- title:
--   Proposition 6.32 -- mconvex_satisfies_gs
-- statement:
--   **Proposition 6.32** (p.153). An M-convex function $f \in M[\mathbb Z\to\mathbb R]$ satisfies (M-GS[Z]): if $x$ minimizes $f[p]$ and $q \ge p$, some minimizer of $f[q]$ agrees with or exceeds $x$ on every coordinate where $p$ and $q$ agree.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.153, Proposition 6.32, Eq. (6.60)-(6.61).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.153, Proposition 6.32

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MGS

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.32 (p.153). -/
theorem mconvex_satisfies_gs (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) : MGS f := by sorry

end DiscreteConvex.MConvexFunctionsC
