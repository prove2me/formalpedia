-- Prove2me | Theorems.Thm_BetterKMedian_KMedian_theorem_1_4
-- name    : BetterKMedian.KMedian.theorem_1_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-13T15:23:13.991758+00:00
-- url     : https://prove2.me/theorems/bb1c5873-900f-4a71-b35d-bcdf795d350a
-- title:
--   Theorem 1.4 ($\beta$-stable algorithm) — a $(1.934+\varepsilon)$-approximation for $\beta$-stable $k$-median in time $\exp(O(\beta^{-1}\mathrm{poly}(1/\varepsilon)))\,n^{\mathrm{poly}(1/\varepsilon)}$
-- statement:
--   This is the stable-instance half of the paper's better-than-2 approximation for $k$-median.
--
--   An instance of metric $k$-median consists of a set $D$ of clients, a nonempty set $F$ of facilities, distances $d$ on $D \cup F$ satisfying the triangle inequality, and an integer $k \ge 1$. For a nonempty $S \subseteq F$, $\mathrm{cost}(S) = \sum_{j \in D} \min_{i \in S} d(i,j)$, and $\mathrm{opt}_\ell$ is the minimum of $\mathrm{cost}(S)$ over nonempty $S \subseteq F$ with $|S| \le \ell$. The instance is **$\beta$-stable** if
--   $$\mathrm{opt}_{k-1} \ge (1+\beta)\,\mathrm{opt}_k,$$
--   that is, if removing one center increases the optimal cost substantially.
--
--   **Theorem.** Let $\beta > 0$ and $\varepsilon \in (0, 1/200)$. There is a randomized algorithm running in time $\exp\bigl(O(\beta^{-1}\,\mathrm{poly}(1/\varepsilon))\bigr)\, n^{\mathrm{poly}(1/\varepsilon)}$ that, on every $\beta$-stable instance with rational distances and $k \le |F|$, with probability at least $1-\varepsilon$ outputs a set $S \subseteq F$ with $|S| = k$ and
--   $$\mathrm{cost}(S) \le (1.934 + \varepsilon)\,\mathrm{opt}_k .$$
--
--   Precisely: there are absolute natural numbers $a, b$ such that for all such $\beta, \varepsilon$ there is a Turing machine that, on an input of length $N$ (the binary code of the instance followed by coin flips), halts within
--   $$T(N) = \exp\!\bigl(a\,\beta^{-1}(1/\varepsilon)^b\bigr)\,(N+2)^{a(1/\varepsilon)^b}$$
--   steps; the number of coins it is given on an instance whose code has length $N$ is also at most $T(N)$.
--
--   Stable instances are what remains after the pseudo-approximation of Theorem 1.2: if opening $O(\log n)$ fewer centers is expensive, some intermediate budget is $\Omega(1/\log n)$-stable, and a running time exponential only in $1/\beta$ is then polynomial. Theorems 1.2 and 1.4 together give Theorem 1.1.
--
--   Differences from the source:
--   - encoding: "there exists an algorithm running in $\exp\{O(\beta^{-1}\mathrm{poly}(1/\varepsilon))\}\,n^{\mathrm{poly}(1/\varepsilon)}$ time" → absolute constants $a, b$, and for each $\beta, \varepsilon$ one `Turing.TM2ComputableInTime` multi-tape Turing machine with finite tape alphabets whose time function is at most $T(N)$ in its input length $N$; reason: $O(\cdot)$ and $\mathrm{poly}(\cdot)$ are absolute; the paper names no machine model; $n$ is replaced by the input length, the standard meaning for bit-encoded instances.
--   - reading: the algorithm may depend on $\beta$ and $\varepsilon$ → the machine is chosen after $\beta$ and $\varepsilon$; reason: the source says "Let … be a $\beta$-stable instance … and $\varepsilon \in (0,1/200)$. There exists an algorithm". The authors' own Lean formalization (`BCFGJPSSV26.stable_kMedian_approximation`, https://github.com/raresbuhai/formalization-of-my-research/tree/main/BCFGJPSSV26) proves a stronger uniform version in which one machine receives $\varepsilon$ and a bound on $1/\beta$ as input.
--   - encoding: "with probability $1-\varepsilon$" → the fraction of coin strings of the given length on which the output is as stated is at least $1-\varepsilon$; the number of coins is bounded by the same $T$; reason: a randomized Turing machine reads its coins from the input.
--   - reading: "outputs $S \subseteq F$ with $|S| = k$" → the hypothesis $k \le |F|$ is added; reason: otherwise no set of exactly $k$ facilities exists.
--   - encoding: $\beta$-stability for $k = 1$ → every instance with $k=1$ is stable; reason: the paper's $\mathrm{opt}_0$ is $+\infty$ (convention $d(j,\emptyset)=+\infty$).
--   - encoding: instances with real data → rational distances, written in binary; "metric" → pseudometric; no standing assumption (3); reason: as in Theorems 1.1 and 1.2.
--   - encoding: the constant $1.934$ → the real `1934 / 1000`; reason: exact value. The paper remarks that its arXiv version proves the stronger constant $1.89$; this statement follows the STOC submission.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/693.pdf, Theorem 1.4, printed p. 3 (PDF 5), restated in §4, printed p. 17 (PDF 19); stability: §2, printed p. 6 (PDF 8)

import Mathlib
import Definitions.Def_BetterKMedian_KMedian_Model

set_option autoImplicit false

namespace BetterKMedian.KMedian

theorem theorem_1_4 :
    ∃ a b : ℕ, ∀ β ε : ℝ, 0 < β → 0 < ε → ε < 1 / 200 →
      ∃ (alg : RatInstance × List Bool → List Bool) (coins : ℕ → ℕ)
        (P : Turing.TM2ComputableInTime RatInstance.encodeWithCoins id alg),
        (∀ κ : P.tm.K, Finite (P.tm.Γ κ)) ∧
        (∀ N : ℕ, (P.time N : ℝ) ≤ stableTimeBound a b β ε N ∧
          (coins N : ℝ) ≤ stableTimeBound a b β ε N) ∧
        ∀ I : RatInstance, I.k ≤ I.facilities.card → I.IsStable β →
          1 - ε ≤ coinProb (coins I.encode.length)
            (fun r => ∃ S : Finset (Fin I.n), alg (I, r) = I.code S ∧ S ⊆ I.facilities ∧
              S.card = I.k ∧ I.cost S ≤ (1934 / 1000 + ε) * I.opt) := by sorry

end BetterKMedian.KMedian
