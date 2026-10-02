-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_m2_l2_conjugacy_correspondence
-- name    : DiscreteConvex.ConjugacyDualityD.m2_l2_conjugacy_correspondence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T02:02:28.336995+00:00
-- url     : https://prove2.me/theorems/58ac1abe-f5fe-4545-955c-722c16c3ed5c
-- title:
--   Theorem 8.48 -- m2_l2_conjugacy_correspondence
-- statement:
--   **Theorem 8.48** (p.234). The M2-convex and L2-convex (and M$^\natural_2$-convex and L$^\natural_2$-convex) classes are in one-to-one correspondence under the discrete Legendre-Fenchel transform: conjugation carries integer-valued M2-convex functions bijectively to integer-valued L2-convex functions (and the M$^\natural_2$/L$^\natural_2$ pair likewise), with biconjugation recovering the original function in each case.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, Theorem 8.48.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, Theorem 8.48

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.48 (p.234). The M2-convex and L2-convex (and M♮₂-convex and L♮₂-convex) classes
are in one-to-one correspondence under the discrete Legendre-Fenchel transform. -/
theorem m2_l2_conjugacy_correspondence :
    (∀ f : (V → ℤ) → WithTop ℝ, M2Convex f → IsIntegerValuedFn f →
      L2Convex (ConvexConjugate f) ∧ ConvexConjugate (ConvexConjugate f) = f) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, L2Convex g → IsIntegerValuedFn g →
      M2Convex (ConvexConjugate g) ∧ ConvexConjugate (ConvexConjugate g) = g) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → IsIntegerValuedFn f →
      LNat2Convex (ConvexConjugate f) ∧ ConvexConjugate (ConvexConjugate f) = f) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNat2Convex g → IsIntegerValuedFn g →
      MNat2Convex (ConvexConjugate g) ∧ ConvexConjugate (ConvexConjugate g) = g) := by sorry

end DiscreteConvex.ConjugacyDualityD
