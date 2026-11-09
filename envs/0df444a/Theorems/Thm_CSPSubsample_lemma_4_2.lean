-- Prove2me | Theorems.Thm_CSPSubsample_lemma_4_2
-- name    : CSPSubsample.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:25:56.904612+00:00
-- url     : https://prove2.me/theorems/05953416-7228-4dd1-acec-ebe6a4683933
-- title:
--   Lemma 4.2 — $f(Z)$ concentrates: $|f(Z)-\mathbb E f(Z)|\le\varepsilon$ w.p. $\ge1-2e^{-\varepsilon^2N/(2k^2)}$
-- statement:
--   Fix $x\in X$, $N\in[n]$ and $\varepsilon>0$, and let $Z\sim\mathcal D(x,N)$ be the empirical mean of $N$ i.i.d. draws from the categorical law $x$ (Definition 4.1). Then, with probability at least $1-2\exp\!\big(-\frac{\varepsilon^2N}{2k^2}\big)$,
--   $$
--   \big|f(Z)-\mathbb E[f(Z)]\big|\le\varepsilon .
--   $$
--   This is the concentration half of the concentration lemma: the sample size needed is polynomial in the arity $k$, the source of the paper's improvement.
--
--   Differences from the source:
--   - encoding: x ∈ X and Z ∼ D(x, N), the empirical mean of N i.i.d. pairs (i_t, a_t) with P[(i_t, a_t) = (i, a)] = x_{i,a} → x = x(ϕ) for an assignment ϕ, and Z the empirical mean of the pairs (s_t, ϕ(s_t)) for a uniform index sequence s ∈ [n]^N; probabilities and E are finite averages over the n^N sequences; reason: under x(ϕ) the pair (i, a) has probability 𝕀{ϕ_i = a}/n, so a draw is (i_t, ϕ(i_t)) with i_t uniform; the law of Z is the same
--   - encoding: arity k (any k ∈ ℕ) → 1 ≤ k; reason: at k = 0 the printed bound exp(−ε²N/(2k²)) has a zero denominator and is undefined
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Lemma 4.2, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_probWR
import Definitions.Def_CSPSubsample_fPoly

set_option autoImplicit false

namespace CSPSubsample

/-- **Lemma 4.2** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.8 = PDF p.10). Fix `x ∈ X`,
`N ∈ [n]` and `ε > 0`, and let `Z ∼ D(x, N)`. With probability at least `1 − 2exp(−ε²N/(2k²))`,
`|f(Z) − E[f(Z)]| ≤ ε`.

**Formalization Note** `x = x(ϕ)` for an assignment `ϕ` (that is `x ∈ X`); `Z = Zemp ϕ s` with
`s` a uniform sequence of `N` indices (the pairs `(s_t, ϕ(s_t))` have law `x(ϕ)`), and the
probability and `E` are finite averages over `s` (`probWR`, `expWR`). `N ∈ [n]` is
`1 ≤ N ≤ n`. `1 ≤ k` excludes the arity `0`, where `ε²N/(2k²)` is undefined. -/
theorem lemma_4_2 {n k q : ℕ} (I : Instance n k q) (ϕ : Fin n → Fin q) (N : ℕ) (hN1 : 1 ≤ N)
    (hNn : N ≤ n) (ε : ℝ) (hε : 0 < ε) (hk : 1 ≤ k) :
    1 - 2 * Real.exp (-(ε ^ 2 * N / (2 * (k : ℝ) ^ 2))) ≤
      probWR n N (fun s => |fPoly I (Zemp ϕ s) - expWR n N (fun s' => fPoly I (Zemp ϕ s'))| ≤ ε) := by sorry

end CSPSubsample
