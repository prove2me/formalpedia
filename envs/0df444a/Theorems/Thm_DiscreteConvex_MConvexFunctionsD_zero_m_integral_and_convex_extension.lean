-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_zero_m_integral_and_convex_extension
-- name    : DiscreteConvex.MConvexFunctionsD.zero_m_integral_and_convex_extension
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:59:46.27754+00:00
-- url     : https://prove2.me/theorems/3c062546-fb17-4ab6-874f-078fd4ffa260
-- title:
--   Proposition 6.56 -- zero_m_integral_and_convex_extension
-- statement:
--   **Proposition 6.56** (p.164). (1) $0M[\mathbb Z|\mathbb R\to\mathbb R] = 0M[\mathbb R\to\mathbb R]$ (arg-min-integrality is automatic for positively homogeneous polyhedral M-convex functions). (2) The convex extension of a function in $0M[\mathbb Z\to\mathbb R]$ belongs to $0M[\mathbb R\to\mathbb R]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Proposition 6.56.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.164, Proposition 6.56

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ConvexClosureVal
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMZR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.56 (p.183). -/
theorem zero_m_integral_and_convex_extension (f : (V → ℝ) → WithTop ℝ)
    (fZ : (V → ℤ) → WithTop ℝ) :
    (ZeroMZR f ↔ ZeroMR f) ∧ (ZeroMZ fZ → ZeroMR (ConvexClosureVal fZ)) := by sorry

end DiscreteConvex.MConvexFunctionsD
