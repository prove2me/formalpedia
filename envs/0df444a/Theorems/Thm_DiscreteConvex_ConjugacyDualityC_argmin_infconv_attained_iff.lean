-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_argmin_infconv_attained_iff
-- name    : DiscreteConvex.ConjugacyDualityC.argmin_infconv_attained_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:43:57.039182+00:00
-- url     : https://prove2.me/theorems/169349d3-dbed-4ad3-9251-506fd98f8ff2
-- title:
--   Proposition 8.41 -- argmin_infconv_attained_iff
-- statement:
--   **Proposition 8.41** (p.230). If the infimal convolution $g_1\square g_2$'s defining infimum is attained whenever finite, then $\arg\min(g_1\square g_2)[-x] = \arg\min g_1[-x] + \arg\min g_2[-x]$ for every $x\in\mathbb R^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.230, Proposition 8.41.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.230, Proposition 8.41

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConvE
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LinearWeight

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.41 (p.230). When the infimal convolution's defining infimum is always attained
when finite, the minimizer set of a linearly-perturbed infimal convolution splits as a Minkowski
sum. `hfin` is the book's `g1 □ g2 > -∞`: `InfConv` takes its infimum in the conditionally
complete `WithTop ℝ` and reads the junk value `0` when the values are unbounded below, and with
`g1(p) = p₁`, `g2(p) = -p₁ + p₂` and `x = 0` the left side is then all of `Zⱽ` while the right
side is the Minkowski sum of two empty sets. -/
theorem argmin_infconv_attained_iff (g1 g2 : (V → ℤ) → WithTop ℝ)
    (hfin : ∀ p : V → ℤ, InfConvE g1 g2 p ≠ ⊥)
    (hattained : ∀ p : V → ℤ, InfConv g1 g2 p ≠ ⊤ →
      ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ InfConv g1 g2 p = g1 p1 + g2 p2) :
    ∀ x : V → ℝ, ArgMin (LinearWeight (InfConv g1 g2) x) =
      ArgMin (LinearWeight g1 x) + ArgMin (LinearWeight g2 x) := by sorry

end DiscreteConvex.ConjugacyDualityC
