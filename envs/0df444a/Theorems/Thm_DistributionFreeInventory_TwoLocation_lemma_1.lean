-- Prove2me | Theorems.Thm_DistributionFreeInventory_TwoLocation_lemma_1
-- name    : DistributionFreeInventory.TwoLocation.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:30:35.356142+00:00
-- url     : https://prove2.me/theorems/0d9e08e9-cf7c-4f3c-8bda-6ec119329d6e
-- title:
--   Lemma 1 — nested recourse decomposition
-- statement:
--   For any positive number $n$ of locations, any $L$-level nested fulfillment hierarchy as in §2, positive holding and penalty costs $h,p$, and positive cluster costs satisfying Assumption 1 non-strictly, let $y,d\in\mathbb R_+^n$. The original shipment optimum in (2) satisfies
--   $$C(y,d)=h\,e^\top(y-d)+s_0^\top d+\sum_{\ell=0}^{L-1}\eta_\ell^\top(E_\ell d-E_\ell y)^+.$$
--   Here $E_\ell$ aggregates coordinates in each level-$\ell$ cluster, the componentwise positive part is $\max(x,0)$, the root increment is $p+h-s_{L-1}$, and every other increment is the parent cost minus the child's cost. Shipment costs are those of first common clusters. The conclusion is an identity with the flow optimum, not its definition.
--
--   Differences from the source:
--   - encoding: numbered nonempty partition blocks and assignment matrices → finite sets of finite clusters, their coordinate sums, and positive n and L; reason: relabeling blocks preserves every nested hierarchy, and L=1 for n=1 is retained
--   - reading: cost at the common cluster in the nested fulfillment structure → cost at the first common cluster, with its unique parent for increments; reason: this is the hierarchy interpretation illustrated on pages 7–8 and used in the lemma’s proof
--   - encoding: real physical recourse optimum → identity in EReal with a nonnegative extended infimum on the left; reason: physical nonnegative y and d admit zero flow, and the positive-cost optimum is finite; the extension also defines the same cost outside the lemma’s domain
-- source:
--   Govindarajan, Sinha & Uichanco, Distribution-Free Inventory Risk Pooling in a Multilocation Newsvendor, DOI 10.1287/mnsc.2020.3719, held source.pdf, Lemma 1, equation (5), printed p. 10 (PDF 10); proof EC.2.1, ec3–ec4 (PDF 36–37)

import Definitions.Def_DistributionFreeInventory_TwoLocation_Hierarchy

namespace DistributionFreeInventory.TwoLocation

theorem lemma_1 {n : ℕ} (H : NestedPartition n)
    (c : ℕ → Finset (Fin n) → ℝ) (h p : ℝ)
    (hh : 0 < h) (hp : 0 < p) (hc : NestedCosts H c h p)
    (y d : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i) :
    (recourse h p (nestedMatrix H c) y d : EReal) =
      (nestedExpression H c h p y d : EReal) := by sorry

end DistributionFreeInventory.TwoLocation
