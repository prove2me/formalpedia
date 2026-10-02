-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsC_conjugate_scaling_preserves_mconvex
-- name    : DiscreteConvex.AlgorithmsC.conjugate_scaling_preserves_mconvex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T04:45:40.762661+00:00
-- url     : https://prove2.me/theorems/e4b7fc91-5169-49ab-b97e-7d78ec37f548
-- title:
--   Proposition 10.41 -- conjugate_scaling_preserves_mconvex
-- statement:
--   **Proposition 10.41** (p.319). GOAL. For a dual-integral polyhedral M-convex function $f=\mathrm{ConjugateFromZ}(g)$ (with $g$ L$^
--   atural$-convex), the conjugate scaling $f\langle\alpha\rangle$ is again dual-integral M-convex — witnessed by $g_\alpha$ itself being L$^
--   atural$-convex — provided $f\langle\alpha\rangle>-\infty$.
--
--   Chosen as goal: this is the enabling fact for the conjugate scaling algorithm, the chapter's final and most refined algorithm for the M-convex submodular flow problem, and is the one "compatible scaling operation" the book's own text singles out as the reason naive scaling of an M-convex function fails while this construction succeeds.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Proposition 10.41.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Proposition 10.41

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_AlgorithmsC_ScaledConjugate
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateFromZ
import Definitions.Def_DiscreteConvex_AlgorithmsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScalingE
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScaling

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.41 (p.319). GOAL. For a dual-integral polyhedral M-convex function
`f = ConjugateFromZ g` (`g` L♮-convex), the conjugate scaling `f⟨α⟩` is again a dual-integral
polyhedral M-convex function, provided `f⟨α⟩ > -∞`. The conclusion is about `f⟨α⟩` itself: it
satisfies (M-EXC[R]) and lies in `M[R→R|Z]`, i.e. it is `ConjugateFromZ` of an L♮-convex function
(`g_α`). L♮-convexity of `g_α` alone is Theorem 7.10 (2) and a lemma of the proof, and leaves
`hprop` unused. -/
theorem conjugate_scaling_preserves_mconvex (g : (V → ℤ) → WithTop ℝ) (hg : LNaturalConvex g)
    (alpha : ℤ) (halpha : 0 < alpha) (hprop : ∀ x, ConjugateScalingE g alpha x ≠ ⊥) :
    MExchangeAxiomR (ConjugateScaling g alpha) ∧
      LNaturalConvex (ScaledConjugate g alpha) ∧
      ConjugateScaling g alpha = ConjugateFromZ (ScaledConjugate g alpha) := by sorry

end DiscreteConvex.AlgorithmsC
