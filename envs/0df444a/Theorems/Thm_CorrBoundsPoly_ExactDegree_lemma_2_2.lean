-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_2_2
-- name    : CorrBoundsPoly.ExactDegree.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:04.089143+00:00
-- url     : https://prove2.me/theorems/f5aad489-fd29-4df1-94a3-6f40ee66dd64
-- title:
--   Lemma 2.2 — square-zero tensor identity $h(T\otimes I+I\otimes S)=h(T)h(S)$ in characteristic two
-- statement:
--   Let $V,W$ be finite-dimensional vector spaces over a field of characteristic two, and let $T:V\to V$ and $S:W\to W$ satisfy $T^2=S^2=0$. For an operator $R$ on a space $U$ put $h(R)=\dim U-2\operatorname{rank}R$. Then $N=T\otimes I_W+I_V\otimes S$ on $V\otimes W$ is square-zero, and
--   $$h(N)=h(T)\,h(S).$$
--
--   The identity can be iterated over any number of tensor factors; it computes the rank of the leading operator of an XOR of disjoint cores from the ranks for the single cores (Theorem 2.3, Lemma 3.4).
--
--   Differences from the source: none.
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 21 (PDF 23), Lemma 2.2

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Filtration

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 2.2** (Square-zero tensor identity; Xin Li, *More on Correlation Bounds for
Polynomials*, p. 21, PDF 23). `V, W` finite-dimensional over a field of characteristic two,
`T² = 0`, `S² = 0`, `h(R) = dim U − 2 rank R`. Then `N = T ⊗ I_W + I_V ⊗ S` is square-zero and
`h(N) = h(T) h(S)`. -/
theorem lemma_2_2 {K V W : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : V →ₗ[K] V) (S : W →ₗ[K] W) (hT : T ∘ₗ T = 0) (hS : S ∘ₗ S = 0) :
    (TensorProduct.map T LinearMap.id + TensorProduct.map LinearMap.id S) ∘ₗ
        (TensorProduct.map T LinearMap.id + TensorProduct.map LinearMap.id S) = 0 ∧
      hOp (TensorProduct.map T LinearMap.id + TensorProduct.map LinearMap.id S) =
        hOp T * hOp S := by sorry

end CorrBoundsPoly.ExactDegree
