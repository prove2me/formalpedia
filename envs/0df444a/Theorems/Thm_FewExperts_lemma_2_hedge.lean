-- Prove2me | Theorems.Thm_FewExperts_lemma_2_hedge
-- name    : FewExperts.lemma_2_hedge
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:52:56.01034+00:00
-- url     : https://prove2.me/theorems/97d24292-2545-4cdf-8471-627046bb0f52
-- title:
--   Lemma 2 — Hedge with rate $\sqrt{\ln n/T}$ has regret $\le 2\sqrt{T\ln n}$ at every prefix time and is shift invariant
-- statement:
--   Let $x_1,\dots,x_n$ be gain streams with $x_j(t)\in[0,1]$ for $t=1,\dots,T$. Run Hedge on them with rate $\eta=\sqrt{\ln n/T}$, and write $g^H_u$ for its gain at round $u$.
--
--   1. For every prefix time $t\le T$ and every stream $j$,
--   $$
--   \sum_{u=1}^t x_j(u)-\sum_{u=1}^t g^H_u\le 2\sqrt{T\ln n}.
--   $$
--   2. Hedge's weights do not change when the same constant is added to every cumulative gain. Its prediction therefore depends only on the differences between the cumulative gains.
--
--   The paper applies this lemma to Hedge on the sampled experts and to the two-expert Hedge on a baseline algorithm and an expert.
--
--   Differences from the source:
--   - reading: there is an algorithm (Hedge, [FS97]) → the concrete Hedge with rate √(ln n/T); reason: the lemma names multiplicative weights; the concrete algorithm implies the existence statement
--   - generalization: N experts → n arbitrary [0, 1]-valued gain streams; reason: an expert is a stream (its gains); the paper uses the lemma with an algorithm as one of the experts
--   - reading: the prediction depends only on the differences between cumulative gains and the random tape → the weights are invariant under adding a constant to every cumulative gain (Hedge has no random tape); reason: a function of a vector is a function of its differences exactly when it is invariant under adding a common constant
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Lemma 2, p.14 (PDF p.15), citing Freund–Schapire 1997, §2

import Mathlib
import Definitions.Def_FewExperts_hedgeWeights

namespace FewExperts

/-- **Lemma 2 (Hedge algorithm (multiplicative weights) [FS97, Section 2]).**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Lemma 2, p.14 (PDF 15): "Consider the problem of predictions with expert advice with
N experts over a horizon of T time steps. Then, there is an algorithm which achieves regret at
most 2√(T ln N) against all experts and all prefix times. Moreover, at each step, the prediction
of the algorithm depends only on the differences between the cumulative gains of the experts so
far, and the random tape of the algorithm."

The algorithm is Hedge with rate `√(ln n / T)` (`hedgeRate n T`), run on `n` gain streams
`x j t ∈ [0, 1]` (rounds `1, …, T`). (1) At every prefix time `t ≤ T` and against every stream
`j`, its regret `∑_{u ≤ t} x j u − ∑_{u ≤ t} (Hedge's gain at u)` is at most `2√(T ln n)`.
(2) Its weights are unchanged when the same constant is added to every cumulative gain, i.e.
they depend only on the differences of the cumulative gains.

**Formalization Note** The experts are arbitrary `[0, 1]`-valued streams, so that the lemma
applies to Hedge run on an algorithm and an expert (Algorithm 3, line 15). Hedge is
deterministic here, so there is no random tape. -/
theorem lemma_2_hedge (n T : ℕ) (x : Fin n → ℕ → ℝ)
    (hx : ∀ j t, 1 ≤ t → t ≤ T → x j t ∈ Set.Icc (0 : ℝ) 1) :
    (∀ t ≤ T, ∀ j, ∑ u ∈ Finset.Icc 1 t, x j u - ∑ u ∈ Finset.Icc 1 t, hedgeGain (hedgeRate n T) x u ≤
        2 * Real.sqrt (T * Real.log n)) ∧
    (∀ (η c : ℝ) (X : Fin n → ℝ), hedgeWeights η (fun j => X j + c) = hedgeWeights η X) := by sorry

end FewExperts
