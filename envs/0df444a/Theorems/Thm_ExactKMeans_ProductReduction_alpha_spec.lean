-- Prove2me | Theorems.Thm_ExactKMeans_ProductReduction_alpha_spec
-- name    : ExactKMeans.ProductReduction.alpha_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T18:46:03.013101+00:00
-- url     : https://prove2.me/theorems/825637f4-1b5c-4538-a7d8-ae70e636e1a0
-- title:
--   The construction angle $\alpha$ is well defined (Section 5)
-- statement:
--   This lemma shows that the angle $\alpha$ fixed in the Section 5 construction is well defined.
--
--   Let $a,b\ge 1$ be integers with $ab\ge 2$, let $t\ge 3$ be odd, and put $N=abt$ and $\lambda=N^{12}-t+1$. The construction chooses a positive angle $\alpha$ with
--
--   $$
--   \frac12<\alpha\lambda<1 \qquad\text{and}\qquad \lambda\sin\alpha=\cos\big((t-1)\alpha\big),
--   $$
--
--   and then sets $r=1/(\sqrt b\,N^{12}\sin\alpha)$. The lemma asserts that such an angle exists. Consequently the chosen $\alpha$ satisfies all of the displayed conditions, and moreover
--
--   $$
--   \sin\alpha>0 \qquad\text{and}\qquad r>0 .
--   $$
--
--   The later quantitative statements of Section 5 involve $\alpha$, $r$ and $\gamma=\alpha r\delta/\sqrt b$ and rely on these defining relations and on positivity. This lemma isolates that fact so that it can be imported once instead of being re-derived in each proof.
--
--   **Formalization Note** In the published definition, $\alpha$ is a choice (`Classical.epsilon`) of a real number satisfying the displayed conditions; without an existence proof it would be an unconstrained real number. The conclusion lists, in order, $0<\alpha$, $\tfrac12<\alpha\lambda$, $\alpha\lambda<1$, the defining equation, $\sin\alpha>0$ and $r>0$.
-- source:
--   Bai, Fomin, Xu (2026), Exact Euclidean k-Means: Faster in the Plane, Hard Beyond It, held STOC 2027 submission; SHA-256 89f18334320ba73627305c6f8870ae70fef423ca012f8b71a3052e407c7e62ec, printed pp. 28–31 (PDF 29–32), Definitions 3–4: choice of the positive angle α with 1/2<αλ<1 and λ sin α=cos((t−1)α), and r=1/(√b N^12 sin α)

import Definitions.Def_ExactKMeans_ProductReduction_Selector

open scoped BigOperators Classical
open Finset
open ExactKMeans.ProductReduction

namespace ExactKMeans.ProductReduction

theorem alpha_spec (p : Parameters) :
    0 < p.alpha ∧ (1 / 2 : ℝ) < p.alpha * p.lam ∧ p.alpha * p.lam < 1 ∧
      (p.lam : ℝ) * Real.sin p.alpha = Real.cos (((p.t : ℝ) - 1) * p.alpha) ∧
      0 < Real.sin p.alpha ∧ 0 < p.r := by sorry

end ExactKMeans.ProductReduction
