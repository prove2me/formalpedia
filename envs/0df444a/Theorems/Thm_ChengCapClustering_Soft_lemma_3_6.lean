-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_3_6
-- name    : ChengCapClustering.Soft.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:20.658968+00:00
-- url     : https://prove2.me/theorems/df8e5f70-997f-4881-a71d-014ff215d87a
-- title:
--   Lemma 3.6 — rescue lemma: $R$, $J_0$ with (i) closed centers unused, (ii) $|R|+|J|-|J_0|\le k+b$, (iii) $\sum_R W_i\ge((b-L)/k-3/(L+1))\sum_I W_i$
-- statement:
--   Let $\pi$ be an integral transport plan between disjoint index sets $I$ and $J$ with $|I|\le 2k-1$ and $|J|\le k$ ($k\ge1$) whose support is a forest, and let $W_i\ge0$ for $i\in I$. For all integers $L\ge1$ and $0\le b\le k$ there are $R\subseteq I$ and $J_0\subseteq J$ with (i) $\pi_{ij}=0$ for all $i\in I\setminus R$, $j\in J_0$; (ii) $|R|+|J|-|J_0|\le k+b$; (iii) $\sum_{i\in R}W_i\ge\big(\frac{b-L}{k}-\frac{3}{L+1}\big)\sum_{i\in I}W_i$, with real subtraction $b-L$.
--
--   Differences from the source:
--   - encoding: disjoint index sets I and J; |I| ≤ 2k − 1; (ii) |R| + |J| − |J₀| ≤ k + b → finite types I, J with support graph on I ⊕ J; card I + 1 ≤ 2k; R.card + card J ≤ k + b + J₀.card; reason: integer forms without natural-number subtraction (J₀ ⊆ J)
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 3.6, printed p. 10 / PDF p. 12

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Clustering

universe u v

namespace ChengCapClustering.Soft

/-- Lemma 3.6 (Rescue lemma), printed p. 10 / PDF p. 12. For an integral transport plan between
disjoint index sets `I` (`|I| ≤ 2k − 1`) and `J` (`|J| ≤ k`) whose support is a forest, savings
`W_i ≥ 0`, and integers `L ≥ 1`, `0 ≤ b ≤ k`, there are `R ⊆ I` and `J₀ ⊆ J` with (i) `π_ij = 0` for
`i ∉ R`, `j ∈ J₀`; (ii) `|R| + |J| − |J₀| ≤ k + b`; (iii) `∑_{i∈R} W_i ≥ ((b − L)/k − 3/(L+1)) ∑_{i∈I} W_i`. -/
theorem lemma_3_6 {I : Type u} {J : Type v} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (π : I → J → ℕ) (k : ℕ) (hk : 0 < k) (hI : Fintype.card I + 1 ≤ 2 * k)
    (hJ : Fintype.card J ≤ k) (hforest : (supportGraph π).IsAcyclic) (W : I → ℝ)
    (hW : ∀ i, 0 ≤ W i) (L b : ℕ) (hL : 1 ≤ L) (hb : b ≤ k) :
    ∃ (R : Finset I) (J₀ : Finset J),
      (∀ i ∉ R, ∀ j ∈ J₀, π i j = 0) ∧
      R.card + Fintype.card J ≤ k + b + J₀.card ∧
      (((b : ℝ) - (L : ℝ)) / (k : ℝ) - 3 / ((L : ℝ) + 1)) * ∑ i, W i ≤ ∑ i ∈ R, W i := by sorry

end ChengCapClustering.Soft
