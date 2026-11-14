-- Prove2me | Theorems.Thm_BetterKMedian_KMedian_theorem_1_1
-- name    : BetterKMedian.KMedian.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-13T15:09:36.747904+00:00
-- url     : https://prove2.me/theorems/a3046d1f-76ed-4ad9-a51c-0131746e78af
-- title:
--   Theorem 1.1 — a randomized polynomial-time $1.95$-approximation algorithm for $k$-median
-- statement:
--   This is the main result of the paper: metric $k$-median can be approximated within a factor below $2$ in polynomial time.
--
--   An instance of metric $k$-median consists of a set $D$ of clients, a nonempty set $F$ of facilities, distances $d$ on $D \cup F$ satisfying the triangle inequality, and an integer $k \ge 1$. For a nonempty $S \subseteq F$, $\mathrm{cost}(S) = \sum_{j \in D} \min_{i \in S} d(i,j)$, and $\mathrm{opt}$ is the minimum of $\mathrm{cost}(S)$ over nonempty $S \subseteq F$ with $|S| \le k$.
--
--   **Theorem.** There is a randomized polynomial-time algorithm that, on every instance with rational distances, always outputs a nonempty set $S \subseteq F$ with $|S| \le k$, and with probability at least $2/3$ over its coin flips
--   $$\mathrm{cost}(S) \le 1.95 \cdot \mathrm{opt}.$$
--
--   Precisely: there are a Turing machine running in time polynomial in its input length and a polynomial $q$ such that, on the binary code of an instance of length $N$ followed by any string of $q(N)$ coin flips, the machine outputs the indicator of a solution with at most $k$ centers, and for at least a $2/3$ fraction of the $2^{q(N)}$ coin strings that solution has cost at most $1.95\cdot\mathrm{opt}$.
--
--   Earlier work of Cohen-Addad, Grandoni, Lee, Schwiegelshohn and Svensson reached the ratio $2 + \varepsilon$; this theorem shows that the factor $2$ is not a barrier. The paper obtains $1.95$ by combining a $(1.9499+\varepsilon)$-pseudo-approximation opening $k + O(\log n/\varepsilon^2)$ centers (Theorem 1.2) with a better-than-2 approximation for stable instances (Theorem 1.4).
--
--   Differences from the source:
--   - encoding: "a randomized polynomial-time algorithm" (no machine model named) → one `Turing.TM2ComputableInPolyTime` multi-tape Turing machine with finite tape alphabets, whose input is the binary code of the instance followed by the coin flips, and a polynomial number $q(N)$ of coins; reason: the paper names no model; this is the standard meaning and the same machine model as the published `BetterKMedian.LMPGreedy.theorem_1_3` and `OAI.MetricKMedian.main_finite_work`.
--   - reading: "randomized … $1.95$-approximation" (no success probability stated) → the output is always a feasible solution and has cost at most $1.95\,\mathrm{opt}$ with probability at least $2/3$; reason: this is the reading of the authors' own Lean formalization of this theorem (`BCFGJPSSV26.kMedian_approximation`, https://github.com/raresbuhai/formalization-of-my-research/tree/main/BCFGJPSSV26), which notes that any constant probability can be raised by repetition, keeping the cheapest output.
--   - encoding: instances with real data → rational distances, written in binary; reason: a Turing machine receives finite input.
--   - reading: "metric distances on $D \cup F$" → a pseudometric on finitely many points, with $D$ and $F$ subsets that may overlap; reason: the paper's own examples place clients at distance $0$ from facilities, and this matches the published facility-location definitions for this paper.
--   - generalization: standing assumption (3), $1 \le d(i,j) \le \mathrm{poly}(|D|)$ (p. 5) → no such assumption; reason: (3) is a reduction step "as in [CGL+25, Lemma 2.1]", not a restriction of the theorem.
--   - reading: "a set $S \subseteq F$ of $k$ open facilities" (§1) → a nonempty $S \subseteq F$ with $|S| \le k$, and $k$ may exceed $|F|$; reason: §2 defines $k$-median with "at most $k$ facilities", and the paper's $d(j,\emptyset) = +\infty$ excludes the empty set.
--   - encoding: the constant $1.95$ → the real `195 / 100`; reason: exact value.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/693.pdf, Theorem 1.1, printed p. 2 (PDF 4); §2, printed pp. 5–6 (PDF 7–8)

import Mathlib
import Definitions.Def_BetterKMedian_KMedian_Model

set_option autoImplicit false

namespace BetterKMedian.KMedian

theorem theorem_1_1 :
    ∃ (alg : RatInstance × List Bool → List Bool) (coins : Polynomial ℕ)
      (P : Turing.TM2ComputableInPolyTime RatInstance.encodeWithCoins id alg),
      (∀ κ : P.tm.K, Finite (P.tm.Γ κ)) ∧
      ∀ I : RatInstance,
        (∀ r : List Bool, r.length = coins.eval I.encode.length →
          I.IsSolutionCode I.k (alg (I, r))) ∧
        (2 / 3 : ℝ) ≤ coinProb (coins.eval I.encode.length)
          (fun r => I.IsApproxCode I.k (195 / 100) (alg (I, r))) := by sorry

end BetterKMedian.KMedian
