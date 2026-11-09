-- Prove2me | Theorems.Thm_CSPSubsample_claim_A_2
-- name    : CSPSubsample.claim_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:25:11.959538+00:00
-- url     : https://prove2.me/theorems/7b36484c-02a1-4aab-b1b4-ebfb20ecb0b8
-- title:
--   Claim A.2 — no collision w.p. $\ge 1-N^2/n$; given no collision, sampling with replacement is uniform
-- statement:
--   Let $U_1$ be a set of $N$ elements sampled uniformly from $[n]$ without replacement, and $U_2$ the set of variables obtained by sampling $N$ elements uniformly with replacement from $[n]$. Let $E=\{|U_2|=N\}$ be the event that $U_2$ has no collisions. Then
--
--   1. $\Pr(E)\ge 1-\dfrac{N^2}{n}$;
--   2. $U_2$ conditioned on $E$ has the same law as $U_1$: for every $A\subseteq[n]$,
--   $$
--   \Pr(U_2=A\mid E)=\begin{cases}\binom nN^{-1}&|A|=N,\\0&\text{otherwise.}\end{cases}
--   $$
--
--   It transfers the concentration lemma from sampling with replacement to the uniform $N$-subsets of the subsampling theorem.
--
--   Differences from the source:
--   - encoding: sampling N variables uniformly with replacement from [n], U the set of unique variables → a uniform sequence s ∈ [n]^N (probability = count / n^N), U the image of s; reason: the N draws are i.i.d. uniform; same law
--   - encoding: U_2 conditioned on E has the law of U_1 → for every A ⊆ [n], P(U_2 = A | E) = 𝕀[|A| = N]/C(n, N), stated under N ≤ n; reason: the law of U_1 is uniform on N-subsets; for N > n, P(E) = 0 and the conditional law is undefined
--   - encoding: n unrestricted → 1 ≤ n; reason: sampling from [n] needs n ≥ 1
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Claim A.2, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_CSPSubsample_probWR

set_option autoImplicit false

namespace CSPSubsample

/-- **Claim A.2** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.27 = PDF p.29). Let `U_1` be a set
of `N` elements sampled uniformly from `[n]` without replacement, and `U_2` the set of variables
resulting from sampling `N` elements with replacement uniformly from `[n]`. Let `E = {|U_2| = N}`
(no collisions). Then (i) `P(E) ≥ 1 − N²/n`; (ii) `U_2` conditioned on `E` has the law of `U_1`.

**Formalization Note** `U_2 = sampleSet s` for `s` uniform on `Fin N → Fin n`. Bullet (ii) is
stated as: for every `A ⊆ [n]`, `P(U_2 = A ∣ E) = 𝕀[|A| = N] / C(n, N)`, which is the law of a
uniform `N`-subset. It assumes `N ≤ n`: otherwise `P(E) = 0` and the conditional law is
undefined. `1 ≤ n` is needed to sample from `[n]`. -/
theorem claim_A_2 (n N : ℕ) (hn : 1 ≤ n) :
    1 - (N : ℝ) ^ 2 / n ≤ probWR n N (fun s => (sampleSet s).card = N) ∧
      (N ≤ n → ∀ A : Finset (Fin n),
        ((Finset.univ.filter fun s : Fin N → Fin n =>
            sampleSet s = A ∧ (sampleSet s).card = N).card : ℝ) /
          ((Finset.univ.filter fun s : Fin N → Fin n => (sampleSet s).card = N).card : ℝ) =
        if A.card = N then 1 / (n.choose N : ℝ) else 0) := by sorry

end CSPSubsample
