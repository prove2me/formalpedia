-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_lemma_4_3
-- name    : EqualSubsetSum.Faster.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:26:32.969201+00:00
-- url     : https://prove2.me/theorems/70382113-2fd4-4157-b864-60f17ccab4be
-- title:
--   Lemma 4.3 — sampled corrections never undercount and miss a tail pair with probability ≤ e^{−16n}
-- statement:
--   Let $y\in\mathbb Z^n$, let the positions be normal, transposed or auxiliary, and let $A'$, $B'$ be lists of distinct vectors using the first-list and second-list digits of these types. Let $d$ be even with $0\le d\le n$ and $1\le j\le d+1$; let $U$, $\omega$, the correction pool $E$, $\hat N$ and $N$ be as in the detector of §4.1.
--
--   1. For every sampling outcome and every $a\in A'$, $\hat N(a)\ge N(a)\ge 0$.
--   2. For each fixed **tail pair** $(a,b)\in A'\times B'$ (equal keys and $c(a,b)>d$),
--   $$\Pr[(a,b)\notin E]\le e^{-16n},$$
--   the probability being over the independent Bernoulli($\omega$) keep decisions on the shared labels.
--
--   This is the correctness core of the sampled-correction detector (Theorem 4.2).
--
--   Differences from the source:
--   - encoding: U(a) computed by a graded counting circuit → U(a) defined as the value the circuit computes, ∑_{b ∈ B', equal key} f_d(c(a,b)) − [a ∈ B']; reason: the circuit identity of §4.1 makes the two equal; the lemma uses only the value
--   - encoding: records of lists of distinct vectors → Finsets of vectors, a record identified with its vector; reason: the lists consist of distinct vectors
--   - encoding: each label kept using u fresh fair bits with probability ω → the product of independent Bernoulli(ω) laws on the shared labels; reason: u fair bits accept with probability exactly 2^{−u} = ω
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 23, Lemma 4.3

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Problem
import Definitions.Def_EqualSubsetSum_Faster_Detector

namespace EqualSubsetSum.Faster

/-- Lemma 4.3 (p. 23), for the detector of §4.1: lists `A'`, `B'` of distinct vectors over
normal, transposed and auxiliary positions (`τ`), an even cutoff `0 ≤ d ≤ n`, `1 ≤ j ≤ d + 1`.
For every sampling outcome and every `a ∈ A'`, `N̂(a) ≥ N(a) ≥ 0`. Each fixed tail pair
(`a ∈ A'`, `b ∈ B'`, equal keys, more than `d` conflicts) is missing from the correction pool
with probability at most `e^{-16n}` under independent `Bernoulli(ω)` keeping of the shared
labels. -/
theorem lemma_4_3 {n : ℕ} (τ : Fin n → PosType) (y : Fin n → ℤ) (A' B' : Finset (Fin n → ℤ))
    (hA : ∀ a ∈ A', ∀ i, FirstDigitOK (τ i) (a i))
    (hB : ∀ b ∈ B', ∀ i, SecondDigitOK (τ i) (b i))
    (d j : ℕ) (hd : Even d) (hdn : d ≤ n) (hj : 1 ≤ j) (hjd : j ≤ d + 1) :
    (∀ keep : sharedLabels τ y j A' B' → Bool, ∀ a ∈ A',
        (partnerCount y B' a : ℤ) ≤ correctedCount τ y d j A' B' keep a ∧
          (0 : ℤ) ≤ partnerCount y B' a) ∧
    (∀ a ∈ A', ∀ b ∈ B', weightedSum a y = weightedSum b y → d < conflicts τ a b →
        keepMeasure (sharedLabels τ y j A' B') (samplingProb n d j)
            {keep | (a, b) ∉ correctionPool τ y d j A' B' keep}
          ≤ ENNReal.ofReal (Real.exp (-(16 * (n : ℝ))))) := by sorry

end EqualSubsetSum.Faster
