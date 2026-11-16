-- Prove2me | Theorems.Thm_FewExperts_Supplement_theorem_5_private_regret
-- name    : FewExperts.Supplement.theorem_5_private_regret
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:56:05.533245+00:00
-- url     : https://prove2.me/theorems/b7800bd7-2299-4608-a209-38dcd711c068
-- title:
--   Theorem 5 — an $\varepsilon$-DP algorithm with expected regret $\widetilde O(\sqrt T+1/\varepsilon)$
-- statement:
--   Consider prediction with expert advice against an oblivious adversary, with $N$ experts, horizon $T$ and gains $g_t^i\in[0,1]$ fixed in advance. Logarithms are base 2.
--
--   There are a constant $C>0$ and thresholds $N_0,T_0$ with the following property. For all $N\ge N_0$, $T\ge T_0$ and every $\varepsilon\in(0,1]$, the algorithm MainDP of Algorithms 5–6, with predictions sampled from its mixtures, satisfies both:
--
--   1. it is **$\varepsilon$-differentially private**: for adjacent gain arrays, the law of its sequence of predictions changes by at most a factor $e^{\varepsilon}$ on every event;
--   2. for every gain array $g\in[0,1]^{T\times N}$, its expected regret is at most
--   $$C\Bigl(\sqrt T\log^2T\log N(\log N+\log\log T)\sqrt{\log\log T+\log\log N}+\frac{\log^9T\log^2N(\log N+\log\log T)^3(\log\log T+\log\log N)}{\varepsilon}\Bigr).$$
--
--   The algorithm runs in polynomial time. Up to polylogarithmic factors this matches the $\widetilde\Omega(\sqrt T+1/\varepsilon)$ lower bound that holds already against stochastic adversaries. Oblivious adversaries are therefore no harder than stochastic ones for private online prediction, even under pure DP.
--
--   **Formalization Note** The constant and thresholds do not depend on $\varepsilon$. Integrability of the regret is part of the conclusion.
--
--   Differences from the source:
--   - reading: there is an efficient ε-differentially private algorithm; it runs in polynomial time → the statement is for the explicit algorithm mainDPAlg of Algorithms 5–6; running time is not formalized; reason: the explicit algorithm implies the existential claim; same reading as the published goal of Theorem 4
--   - reading: Lemmas 3–5 are cited mechanisms ([AS17], [DR14]) → pinned standard instances: padded binary tree with Lap(4 log H/ε₀) noise, Hedge with rate √(ln n/H) on the noisy prefix sums, AboveThreshold with Lap(2/ε_sv) and Lap(4/ε_sv); reason: the paper leaves the mechanisms as black boxes; these instances have the cited guarantees; the paper's algorithm is ambiguous only in which instance is used
--   - encoding: O(·) and "T and N sufficiently large" → ∃ C > 0, ∃ N₀ T₀, chosen before ε; reason: standard reading, as in the published goal
--   - encoding: 𝒟(i) ∝ exp(−η a^i_{t0}) with a^i_{t0} = E_S[G^alg_{t0}] − G^i_{t0} + L₀ → 𝒟(i) = exp(η G^i_{t0}) / ∑_k exp(η G^k_{t0}); reason: the i-independent term cancels; the same distribution
--   - encoding: mixed predictions; output = sequence of predictions → the algorithm plays an expert sampled from each mixture; DP is for the law of the sequence of played experts; reason: sampling has the same expected regret against an oblivious adversary (p.13); the plays are the predictions of the protocol
--   - encoding: floors and ceilings omitted; base-2 logarithms; Laplace and sampling draws → ⌈2¹¹rs/α⌉ epochs per scale, ⌈2r⌉ scales, m = ⌈4r/q⌉, K = ⌊1/α⌋; lg = log₂; inverse-CDF transforms of uniform variables; reason: the paper omits floors and ceilings (p.13); same laws
--   - encoding: expected regret E[R] → integrability of the regret is part of the conclusion, then the Bochner integral; reason: excludes a vacuous bound from a non-integrable regret
--   - encoding: Pr[M(x) ∈ V] ≤ e^ε Pr[M(x′) ∈ V] for every measurable V → the inequality between the (outer) measures μ{ω | plays ∈ V} for every set V ⊆ (Fin T → Fin N), adjacency over rounds 1..T of gain arrays in [0, 1]; reason: the output space is finite, so every V is measurable; for a measurable algorithm these are the probabilities of the paper
--   - encoding: N experts → a [NeZero N] binder after N ≥ N₀; reason: the sampling device needs a default expert; it excludes only N = 0, which N₀ ≥ 1 excludes anyway
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Theorem 5, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_FewExperts_Supplement_IsOnlineDP
import Definitions.Def_FewExperts_Supplement_mainDPAlg

namespace FewExperts.Supplement

open MeasureTheory

/-- **Theorem 5: an ε-differentially private algorithm with Õ(√T + 1/ε) expected regret.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Theorem 5, p.23 (PDF 24): "For the problem of oblivious-adversary predictions with
expert advice, for any 0 < ε ≤ 1, there is an ε-differentially private algorithm which achieves
expected regret O(√T log²T log N (log N + log log T) √(log log T + log log N) + log⁹T log²N
(log N + log log T)³ (log log T + log log N)/ε). The algorithm runs in polynomial time."

There are a constant `C > 0` and thresholds `N₀`, `T₀` such that for all `N ≥ N₀`, `T ≥ T₀` and
every `ε ∈ (0, 1]`, the algorithm `mainDPAlg N T ε` of Algorithms 5–6 (with predictions sampled from
its mixtures) satisfies:

1. it is ε-differentially private: for adjacent gain arrays (differing in one round) in
   `[0, 1]^{T × N}`, the law of its sequence of plays changes by at most a factor `e^ε` on every set;
2. for every gain array `g ∈ [0, 1]^{T × N}` fixed in advance (oblivious adversary), its regret is
   integrable and its expected regret is at most `C` times the rate above (`rateDP`).

**Formalization Note** Logs are base 2. The `O(·)` and "T and N sufficiently large" (p.13) are
`∃ C, N₀, T₀`, chosen before `ε`. "There is an efficient algorithm" is stated for the explicit
algorithm of Algorithms 5–6; the running time is not formalized. -/
theorem theorem_5_private_regret :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ T₀ : ℕ, ∀ N T : ℕ, N₀ ≤ N → T₀ ≤ T → ∀ [NeZero N],
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOnlineDP lawDP (mainDPAlg N T ε) T ε ∧
        ∀ g : ℕ → Fin N → ℝ, IsGainSeq T g →
          Integrable (fun ω => gainRegret T g (playDP N T ε ω g)) lawDP ∧
          ∫ ω, gainRegret T g (playDP N T ε ω g) ∂lawDP ≤ C * rateDP N T ε := by sorry

end FewExperts.Supplement
