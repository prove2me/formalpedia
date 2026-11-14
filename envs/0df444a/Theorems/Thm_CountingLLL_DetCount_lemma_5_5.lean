-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_5_5
-- name    : CountingLLL.DetCount.lemma_5_5
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T06:20:17.986723+00:00
-- url     : https://prove2.me/theorems/97b6ad21-b1c1-40fe-964c-00c1f15cae57
-- title:
--   Rooted connected-set count with Cayley coefficient (Lemma 5.5)
-- statement:
--   In a locally finite graph of maximum degree at most Delta>=1, the family of connected induced vertex sets of size t>=1 containing a fixed root is finite, and its cardinality is at most (t^(t-1)/t!) Delta^(t-1). This is the sharper rooted connected-set bound used in the randomized estimator second-moment analysis. The theorem is open; the paper cites a Cayley-tree counting proof.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, Lemma 5.5, Section 5.2.2, PDF p.18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

theorem CountingLLL.DetCount.lemma_5_5 {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (Δ : ℕ) (hΔpos : 1 ≤ Δ) (hΔ : ∀ u, G.degree u ≤ Δ) (v : V) (t : ℕ) (ht : 1 ≤ t) :
    {S : Finset V | v ∈ S ∧ S.card = t ∧ (G.induce (S : Set V)).Connected}.Finite ∧
    (({S : Finset V | v ∈ S ∧ S.card = t ∧ (G.induce (S : Set V)).Connected}.ncard : ℕ) : ℝ) ≤
      ((t : ℝ) ^ (t-1) / (Nat.factorial t : ℝ)) * (Δ : ℝ) ^ (t-1) := by sorry
