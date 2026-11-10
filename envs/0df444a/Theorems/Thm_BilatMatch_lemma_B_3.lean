-- Prove2me | Theorems.Thm_BilatMatch_lemma_B_3
-- name    : BilatMatch.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:13:37.665276+00:00
-- url     : https://prove2.me/theorems/9fee0af0-9dfe-4b60-b4fc-99fbe4f9bc56
-- title:
--   Lemma B.3 (Positive-Part Comparison after Regularization) — $\mathbb E[(x-\hat C)_+]\ge\mathbb E[(x-C)_+]$
-- statement:
--   Fix $\alpha\ge0$ and a finitely supported seller prior $F_S$. Let $C\sim F_S$ and $\hat C\sim\hat F_S$ be the original and reconstructed seller costs. For every threshold $x\in\mathbb R$,
--   $$\mathbb E[(x-\hat C)_+]\ \ge\ \mathbb E[(x-C)_+].$$
--
--   Applied seller by seller, this shows that regularization weakly increases the first best.
--
--   Differences from the source: none.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.3, p.32 (pdf p.34)

import Mathlib
import Definitions.Def_BilatMatch_reconLaw

open MeasureTheory

namespace BilatMatch

/-- **Lemma B.3 (Positive-Part Comparison after Regularization).** Liu, Qin, Wang, arXiv:2609.30702
(held version, sha256 ff1490ad…), Lemma B.3, p.32 (pdf p.34).

Let `C ∼ F_S` (finitely supported) and `Ĉ ∼ F̂_S` be the original and reconstructed seller costs
(`α ≥ 0`). For every threshold `x`, `E[(x − Ĉ)_+] ≥ E[(x − C)_+]`. -/
theorem lemma_B_3 (α : ℝ) (hα : 0 ≤ α) (μ : Measure ℝ) (hμ : IsFiniteSupport μ) (x : ℝ) :
    ∫ c, max (x - c) 0 ∂μ ≤ ∫ c, max (x - c) 0 ∂(reconLaw α μ) := by sorry

end BilatMatch
