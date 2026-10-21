-- Prove2me | Theorems.Thm_FlagshipMEA_Monopoly_lemma_3
-- name    : FlagshipMEA.Monopoly.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:19.670195+00:00
-- url     : https://prove2.me/theorems/0bd8cfd2-01f3-4432-8e53-53a6c366c834
-- title:
--   Lemma 3 — weighted ratio bound and equality case
-- statement:
--   Let $a_i\geq0$, $b_i>0$, and $m_i\geq0$ for a nonempty finite index set, with positive total weight $\sum_i m_i>0$. Choose $k$ attaining the largest component ratio $a_i/b_i$. Lemma 3 states
--
--   $$\frac{\sum_i m_i a_i}{\sum_i m_i b_i}\leq\frac{a_k}{b_k}=\max_i\frac{a_i}{b_i},$$
--
--   with equality precisely when $m_i=0$ for every $i$ that does not attain the maximum. The equality condition identifies which products may receive effort in a revenue maximizing allocation.
--
--   **Formalization Note** The positive total weight excludes the undefined zero over zero ratio at the all-zero allocation. A nonempty product set makes the maximum attainable.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), p. 40 (PDF 42), Lemma 3, (C–1)

import Mathlib

namespace FlagshipMEA.Monopoly

/-- Lemma 3 (p. 40): the weighted ratio is bounded by its largest component ratio,
with equality exactly when all positive weights are on maximizers. -/
theorem lemma_3 {n : ℕ} (hn : 0 < n) (a b m : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) (hm : ∀ i, 0 ≤ m i)
    (hM : 0 < ∑ i, m i) :
    ∃ k : Fin n,
      (∀ i, a i / b i ≤ a k / b k) ∧
      (∑ i, m i * a i) / (∑ i, m i * b i) ≤ a k / b k ∧
      ((∑ i, m i * a i) / (∑ i, m i * b i) = a k / b k ↔
        ∀ i, m i ≠ 0 → a i / b i = a k / b k) := by sorry

end FlagshipMEA.Monopoly
