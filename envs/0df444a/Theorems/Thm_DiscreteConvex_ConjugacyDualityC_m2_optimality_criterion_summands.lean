-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_m2_optimality_criterion_summands
-- name    : DiscreteConvex.ConjugacyDualityC.m2_optimality_criterion_summands
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:43:40.373436+00:00
-- url     : https://prove2.me/theorems/34034f37-ed10-4098-bae9-0162b9aad59d
-- title:
--   Theorem 8.33 -- m2_optimality_criterion_summands
-- statement:
--   **Theorem 8.33** (M2-optimality criterion; p.228). For M-convex $f_1,f_2$ and $x\in\operatorname{dom} f_1\cap\operatorname{dom} f_2$: $x$ globally minimizes $f_1+f_2$ iff a nonnegative-sum condition holds for every disjoint pair of index families $u_1,\ldots,u_k,v_1,\ldots,v_k$ (cyclic, $u_{k+1}=u_1$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.228, Theorem 8.33.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.228, Theorem 8.33

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MExchangeAxiom

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.33 (M2-optimality criterion; p.228). Global optimality of `f1+f2` is characterized
by a nonnegative-sum condition over disjoint cyclic exchanges. -/
theorem m2_optimality_criterion_summands (f1 f2 : (V → ℤ) → WithTop ℝ) (hf1 : MExchangeAxiom f1)
    (hf2 : MExchangeAxiom f2) (x : V → ℤ) (hx : x ∈ DomZ f1 ∩ DomZ f2) :
    (∀ y : V → ℤ, f1 x + f2 x ≤ f1 y + f2 y) ↔
      (∀ k : ℕ, ∀ u v : Fin (k + 1) → V, (∀ i j, u i ≠ v j) →
        (∑ i : Fin (k + 1),
            (f1 (fun w => x w - IndicatorVec {u i} w + IndicatorVec {v i} w) - f1 x)) +
          (∑ i : Fin (k + 1),
            (f2 (fun w => x w + IndicatorVec {u (i + 1)} w - IndicatorVec {v i} w) - f2 x)) ≥
          0) := by sorry

end DiscreteConvex.ConjugacyDualityC
