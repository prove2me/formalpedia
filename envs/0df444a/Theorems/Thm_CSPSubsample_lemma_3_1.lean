-- Prove2me | Theorems.Thm_CSPSubsample_lemma_3_1
-- name    : CSPSubsample.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:26:56.361785+00:00
-- url     : https://prove2.me/theorems/44a4da2c-f308-4c0c-b4ee-10ff43d22a5c
-- title:
--   Lemma 3.1 (Concentration Lemma) — $|\mathrm{val}_U(\phi)-\mathrm{val}(\phi)|\le\varepsilon+k^2/N+\mathbb I[|U|\ne N]$
-- statement:
--   Let $\phi\in[q]^n$ be an assignment. Sample $N$ variables uniformly with replacement from $[n]$ and let $U$ be the resulting set of unique variables. For any $\varepsilon>0$, with probability at least $1-2\exp\!\big(-\frac{\varepsilon^2N}{2k^2}\big)$,
--   $$
--   \big|\mathrm{val}_U(\phi)-\mathrm{val}(\phi)\big|\le\varepsilon+\frac{k^2}{N}+\mathbb I\big[|U|\neq N\big].
--   $$
--   The indicator makes the bound vacuous when the sample repeats a variable. This is the first of the two lemmas the subsampling theorem combines; it is applied once to the original CSP and once, inside Lemma 5.4, to a derived CSP of arity $k-1$.
--
--   Differences from the source:
--   - encoding: sampling N variables uniformly with replacement from [n], U the set of unique variables → a uniform sequence s ∈ [n]^N (probability = count / n^N), U the image of s; reason: the N draws are i.i.d. uniform; same law
--   - encoding: n, N, k unrestricted → 1 ≤ n, 1 ≤ N, 1 ≤ k; reason: sampling from [n] needs n ≥ 1, and the printed k²/N and exp(−ε²N/(2k²)) are undefined at N = 0 and k = 0
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Lemma 3.1, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_val
import Definitions.Def_CSPSubsample_valOn
import Definitions.Def_CSPSubsample_probWR

set_option autoImplicit false

namespace CSPSubsample

/-- **Lemma 3.1 (Concentration Lemma)** (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.6 = PDF p.8).
Let `ϕ ∈ [q]^n` be an assignment. Sample `N` variables uniformly with replacement from `[n]` and
let `U` be the resulting set of unique variables. For any `ε > 0`, with probability at least
`1 − 2exp(−ε²N/(2k²))`, `|val_U(ϕ) − val(ϕ)| ≤ ε + k²/N + 𝕀[|U| ≠ N]`.

**Formalization Note** The sample is a uniform sequence `s : Fin N → Fin n` and `U` its image
(`sampleSet`); the probability is `probWR`. There is no `N ≤ n` (for `N > n` the indicator is
`1`). `1 ≤ n` (sampling from `[n]` needs `[n] ≠ ∅`), `1 ≤ N` (`k²/N`) and `1 ≤ k` (`ε²N/(2k²)`)
exclude the inputs where the printed statement is undefined. -/
theorem lemma_3_1 {n k q : ℕ} (I : Instance n k q) (ϕ : Fin n → Fin q) (N : ℕ) (hn : 1 ≤ n)
    (hN : 1 ≤ N) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-(ε ^ 2 * N / (2 * (k : ℝ) ^ 2))) ≤
      probWR n N (fun s => |valOn I (sampleSet s) ϕ - val I ϕ| ≤
        ε + (k : ℝ) ^ 2 / N + (if (sampleSet s).card ≠ N then 1 else 0)) := by sorry

end CSPSubsample
