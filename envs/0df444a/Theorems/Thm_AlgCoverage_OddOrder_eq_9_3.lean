-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_eq_9_3
-- name    : AlgCoverage.OddOrder.eq_9_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:24.450651+00:00
-- url     : https://prove2.me/theorems/cd45287d-baa3-44e7-b85a-7164e2966673
-- title:
--   §9.2, Eq. (9.3) — collision transfer: $q_k=\Pr(D_k^c)\le k(k-1)/(2N)$ and $|\Pr(A\mid D_k)-\Pr(A)|\le q_k$
-- statement:
--   Let $G$ be a finite group of order $N$ and $X\in G^k$ iid uniform inputs; let $D_k$ be the event that the inputs are distinct. Then
--   $$q_k:=\Pr(D_k^c)\le\frac{k(k-1)}{2N},\qquad \big|\Pr(A\mid D_k)-\Pr(A)\big|\le q_k\quad\text{for every input event }A. \tag{9.3}$$
--   Conditional on $D_k$ the law of the inputs is exactly the ordered-distinct law, so $\Pr(A\mid D_k)=\Pr_{\rm od}(A)$. This transfers coverage events from the iid model to sampling without replacement.
--
--   Differences from the source:
--   - generalization: G a finite group of odd order (§9) → G any finite group; reason: §2.1 (p. 6) states the same comparison for every finite group; the odd-order case is a specialization
--   - encoding: Pr(A | D_k) → probOd G k A = #{injective x with A x}/#{injective x}; reason: this is the conditional probability; for k > N, where D_k is empty and the conditional is undefined, probOd is the junk value 0 and q_k = 1, so the inequality holds trivially there
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 28 (PDF 29), §9.2, Eq. (9.3); p. 6 (PDF 7), §2.1

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage

namespace AlgCoverage.OddOrder

/-- §9.2, Eq. (9.3) (collision transfer), Lin, printed p. 28 / PDF 29 (also §2.1, printed p. 6 / PDF 7).
For iid uniform inputs `X ∈ G^k` in a finite group of order `N`, let `D_k` be the event of distinct
inputs. Then `q_k = Pr(D_kᶜ) ≤ k(k − 1)/(2N)`, and for every input event `A`,
`|Pr(A | D_k) − Pr(A)| ≤ q_k`; the conditioned law `Pr(· | D_k)` is the ordered-distinct law `probOd`. -/
theorem eq_9_3 (G : Type*) [Group G] [Fintype G] (k : ℕ) :
    probIid G k (fun x => ¬ Function.Injective x) ≤
        (k : ℝ) * ((k : ℝ) - 1) / (2 * (Fintype.card G : ℝ)) ∧
    ∀ A : (Fin k → G) → Prop,
      |probOd G k A - probIid G k A| ≤ probIid G k (fun x => ¬ Function.Injective x) := by sorry

end AlgCoverage.OddOrder
