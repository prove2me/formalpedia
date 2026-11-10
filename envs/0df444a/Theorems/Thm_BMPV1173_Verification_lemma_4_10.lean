-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_4_10
-- name    : BMPV1173.Verification.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:04:10.626944+00:00
-- url     : https://prove2.me/theorems/7b7b59b8-918f-4acd-9644-e6c61620ff34
-- title:
--   Lemma 4.10 — both prefix total-work bounds
-- statement:
--   Condition on the good events of Lemmas 4.4 and 4.8. For a nonempty $I\subseteq V_a$ with $r=|I|$, define $\mathrm{work}_{ij}$ using (4.23), including the end sentinel $n+1$, and define $\mathrm{work}_j=\sum_{i\in I\setminus\{j\}}\mathrm{work}_{ij}$. There is a universal coefficient for both bounds
--   $$\sum_{j\ne i}\mathrm{work}_{ij}=O(n(a+s))\quad(i\in I),\qquad \sum_j\mathrm{work}_j=O(nr(a+s)).$$
--   The work counts coordinates only through the first common one. For an orthogonal pair it includes the full coordinate set and its termination sentinel. The individual work values are analytical quantities, not information supplied to the searches.
--
--   Differences from the source:
--   - encoding: bit entries indexed by [n] → Boolean functions on Fin n, with a matrix selector when needed; reason: the index bijection preserves every bit and every input instance
--   - generalization: samples drawn at the prescribed sampling scales → any sample lengths and coordinate lists for which the same simultaneous good events hold; reason: the deterministic total-work result specializes to every successful source sample and does not require its probability law
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 4.10, printed p.30 = PDF p.30.

import Definitions.Def_BMPV1173_Verification_Preprocessing

namespace BMPV1173.Verification

open scoped BigOperators

/-- Both total-work inequalities (4.24), with the conditioning of p.29.
The work is the prefix work including the n+1 sentinel, never the whole search set. -/
theorem lemma_4_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n s t d m a : ℕ),
      1 ≤ n → 1 ≤ s → s ≤ n → 1 ≤ t → t ≤ n →
      ∀ (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n)
        (K : Fin m → Fin n) (I : Finset (Fin n)),
      preprocessingGood x p g t → sizeGood (left x p g t) s t K →
      2*t ≤ a → a ≤ 4*n → (∃ b : ℕ, a = 2^b) → I.Nonempty →
      I ⊆ sizeClass (left x p g t) t K a →
      (∀ i ∈ I, (∑ j ∈ Finset.univ.erase i, (pairWork x p g t i j : ℝ)) ≤
        C*(n : ℝ)*(a+s)) ∧
      (∑ j : Fin n, (partnerWork x p g t I j : ℝ)) ≤
        C*(n : ℝ)*I.card*(a+s) := by sorry

end BMPV1173.Verification
