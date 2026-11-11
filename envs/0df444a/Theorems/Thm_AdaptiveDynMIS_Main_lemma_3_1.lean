-- Prove2me | Theorems.Thm_AdaptiveDynMIS_Main_lemma_3_1
-- name    : AdaptiveDynMIS.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:55:34.7792+00:00
-- url     : https://prove2.me/theorems/92d324af-14c6-4c8e-9df4-83eb6e9ce872
-- title:
--   Lemma 3.1 — BernoulliSample selects each element independently with probability p, with at most s + 1 geometric draws
-- statement:
--   Let $S$ be an indexed set and $p\in(0,1]$, and run Algorithm 1 ($\mathrm{BernoulliSample}(S,p)$) with independent $\mathrm{Geo}(p)$ values. Then the returned set $T$ contains each element of $S$ independently with probability $p$:
--   $$\Pr[T=A]=p^{|A|}(1-p)^{|S|-|A|}\qquad\text{for every }A\subseteq S .$$
--   Moreover, on every run, if $|T|=s$, the algorithm makes at most $s+1$ geometric draws and at most $s$ calls to $\mathrm{select}$, so its running time is $\tilde O(1+s)$.
--
--   This is the sampling primitive behind every high domination edge list and reverse list of the algorithm: it samples a set in time proportional to the sample, not to the set.
--
--   **Formalization Note.** The law is `outcomeProb` of the published `SpectralSparsify_Sampling_BernoulliSubset` with constant probability $p$. Geometric values are an exact primitive, read from an i.i.d. $\mathrm{Geo}(p)$ sequence.
--
--   Differences from the source:
--   - reading: $\mathrm{Geo}(p)$ "can be generated in $\tilde O(1)$ time from independent random bits … to $O(\log n)$ bits of precision" → $\mathrm{Geo}(p)$ is an exact primitive, Algorithm 1 reads i.i.d. $\mathrm{Geo}(p)$ values; reason: the lemma is about Algorithm 1, whose step 3 draws $\mathrm{Geo}(p)$; the generation remark precedes the lemma and gives only an approximation of an irrational $p$ (INSIGHTS I1)
--   - reading: running time $\tilde O(1+s)$ → at most $s+1$ geometric draws and at most $s$ select calls on every run; reason: each loop iteration costs one draw and $O(1)$ other work, a draw costs $\tilde O(1)$ and a select $O(\log n)$ (§3), so the counts are the content of the bound; the cost of the primitives is not modelled
--   - encoding: an indexed set with $\mathrm{select}(S,i)$ → a duplicate-free list with $\mathrm{select}(S,i)$ its entry at position $i-1$; reason: an indexed set is a set with an arbitrary order
--   - encoding: "includes each element of $S$ independently with probability $p$" → $\Pr[T=A]=p^{|A|}(1-p)^{|S|-|A|}$ for every $A\subseteq S$; reason: this is the joint law of independent Bernoulli($p$) inclusions
--   - generalization: an indexed set is "a set $S$ of size at most $n$" (§3) whose elements are vertices → a duplicate-free list of any finite length over any type with decidable equality; reason: the size cap only serves the $O(\log n)$ cost of select, which the counts do not model; the statement specializes to every indexed set of size at most $n$
-- source:
--   Chen, Fan, Zhang, Faster Dynamic Maximal Independent Set against Adaptive Adversaries, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), p. 20, Lemma 3.1

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_AdaptiveDynMIS_Main_BernoulliSample

namespace AdaptiveDynMIS.Main

/-- **Lemma 3.1** (Bernoulli sampling) (Chen, Fan, Zhang, arXiv:2611.05932 (PDF sha256
a65b11d9…ec4a), p. 20 (PDF 22)). For an indexed set `S` (a duplicate-free list) and `p ∈ (0, 1]`,
with i.i.d. `Geo(p)` values: the returned set `T` has the law of independent Bernoulli(`p`) selection
of the elements of `S`, i.e. `Pr[T = A] = p^{|A|} (1 - p)^{|S| - |A|}` for every `A ⊆ S`; and on every
run, if `|T| = s`, Algorithm 1 makes at most `s + 1` geometric draws and at most `s` `select`
calls. -/
theorem lemma_3_1 {α : Type*} [DecidableEq α] (S : List α) (hS : S.Nodup) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p ≤ 1) :
    (∀ A ⊆ S.toFinset,
      geoSeqMeasure p {g | (bernoulliSample S g).1 = A} =
        ENNReal.ofReal (SpectralSparsify.Sampling.outcomeProb S.toFinset (fun _ => p) A)) ∧
    ∀ g : ℕ → ℕ,
      (bernoulliSample S g).2.1 ≤ (bernoulliSample S g).1.card + 1 ∧
        (bernoulliSample S g).2.2 ≤ (bernoulliSample S g).1.card := by sorry

end AdaptiveDynMIS.Main
