-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_l2_convex_biconjugate
-- name    : DiscreteConvex.ConjugacyDualityC.l2_convex_biconjugate
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:44:05.011683+00:00
-- url     : https://prove2.me/theorems/1084eabc-de76-4054-a5d1-6f0b264f398b
-- title:
--   Theorem 8.46 -- l2_convex_biconjugate
-- statement:
--   **Theorem 8.46** (p.233). For integer-valued L$^\natural$-convex $g_1,g_2$, the biconjugate of $g_1\square g_2$ recovers $g_1\square g_2$.
--
--   **Not in this chunk's own `BRIEF.md` table** — found by direct reading, immediately following Theorem 8.45 and ending this chunk's own assigned page range (PDF251) exactly where chapter 8's §8.3 also ends. See `STATUS.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.233, Theorem 8.46.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.233, Theorem 8.46

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegerValuedFn

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.46 (p.233). For integer-valued L♮-convex `g1,g2`, the biconjugate of `g1□g2`
recovers `g1□g2`. -/
theorem l2_convex_biconjugate (g1 g2 : (V → ℤ) → WithTop ℝ) (hg1 : LNaturalConvex g1)
    (hg2 : LNaturalConvex g2) (hg1z : IsIntegerValuedFn g1) (hg2z : IsIntegerValuedFn g2) :
    ConvexConjugate (ConvexConjugate (InfConv g1 g2)) = InfConv g1 g2 := by sorry

end DiscreteConvex.ConjugacyDualityC
