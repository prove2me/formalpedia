-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_m2_convex_conjugate
-- name    : DiscreteConvex.ConjugacyDualityC.m2_convex_conjugate
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:45:56.751133+00:00
-- url     : https://prove2.me/theorems/1052be40-8604-4163-9bd8-1a5667eade9d
-- title:
--   Theorem 8.36 -- m2_convex_conjugate
-- statement:
--   **Theorem 8.36** (p.229). For integer-valued M$^\natural$-convex $f_1,f_2$ with $\operatorname{dom} f_1\cap\operatorname{dom} f_2\ne\emptyset$: $(f_1+f_2)^\bullet = f_1^\bullet\square f_2^\bullet$ and $(f_1+f_2)^{\bullet\bullet}=f_1+f_2$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, Theorem 8.36.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, Theorem 8.36

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegerValuedFn

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.36 (p.229). For integer-valued M♮-convex `f1,f2`, `(f1+f2)• = f1•□f2•` and the
biconjugate of `f1+f2` recovers `f1+f2`. -/
theorem m2_convex_conjugate (f1 f2 : (V → ℤ) → WithTop ℝ) (hf1 : MNaturalConvex f1)
    (hf2 : MNaturalConvex f2) (hf1z : IsIntegerValuedFn f1) (hf2z : IsIntegerValuedFn f2)
    (hdom : (DomZ f1 ∩ DomZ f2).Nonempty) :
    ConvexConjugate (fun x => f1 x + f2 x) = InfConv (ConvexConjugate f1) (ConvexConjugate f2) ∧
    ConvexConjugate (ConvexConjugate (fun x => f1 x + f2 x)) = fun x => f1 x + f2 x := by sorry

end DiscreteConvex.ConjugacyDualityC
