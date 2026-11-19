-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lll_size_reduction_bit_clock
-- name    : EdgeSublinearMWIS.Main.lll_size_reduction_bit_clock
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:16:26.80636+00:00
-- url     : https://prove2.me/theorems/ccbdc901-ad54-4ddd-b73d-7092f86404ad
-- title:
--   LLL size reduction: polynomial bit clock and intermediate-state size
-- statement:
--   Let $b_0,\ldots,b_{n-1}\in\mathbb R^n$ be linearly independent integer vectors. Suppose all their initial Gram determinants satisfy $1\le D_k\le2^H$ and every row has norm at most $(n+1)(2^H+1)$. Let $A$ be their canonical signed rational word representation, with encoded size $L$. There are universal natural constants $C>0$ and $q$, independent of $n,H,b,A$, such that the specified complete size-reduction pass satisfies
--   $$
--   \operatorname{time}(A)\le C(L+n+H+4)^q,\qquad
--   \operatorname{size}(\operatorname{SizeReduce}(A))\le C(L+n+H+4)^q.
--   $$
--   The clock includes exact Gram--Schmidt initialization and all row reductions. This gives the uniform arithmetic stage bound needed for the integer LLL implementation used in binary-hull feasibility.
-- source:
--   Exact implementation theorem sizePassCode_polynomial_time (LLLSizePassClock.lean), for sizePassCodeRealizer in Definitions.Def_EdgeSublinearMWIS_Main_BinaryOracleImplementation. Integer Gram-determinant and row-norm hypotheses are explicit. Standard size reduction from Lenstra--Lenstra--Lovasz, Factoring polynomials with rational coefficients, 1982, https://doi.org/10.1007/BF01457454. This arithmetic stage supports the exact-feasibility argument in Bonnet--Chang Section 5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf.

import Definitions.Def_EdgeSublinearMWIS_Main_BinaryOracleImplementation
open scoped BigOperators
open LLLFactor.RedBasis LLLFactor.Reduction
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds EdgeSublinearMWIS.Main.LLLBounds

theorem EdgeSublinearMWIS.Main.lll_size_reduction_bit_clock :
     ∃ C q : ℕ,0< C ∧ ∀ (n H : ℕ) (b : Fin n → Vec n),
       LinearIndependent ℝ b → IntegralRows b →
       (∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H) →
       (∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) → ∀ (A : Fin n → SignedVector),
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,VectorCanonical (A k)) →
       sizePassCodeRealizer.time (List.ofFn A)≤ C*(volume (List.ofFn A)+n+H+4)^q ∧
       volume (sizePassCode (List.ofFn A))≤ C*(volume (List.ofFn A)+n+H+4)^q := by sorry
