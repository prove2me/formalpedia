-- Prove2me | Theorems.Thm_BetterKMedian_KMedian_theorem_1_2
-- name    : BetterKMedian.KMedian.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-13T15:22:49.722893+00:00
-- url     : https://prove2.me/theorems/175dfd67-d7da-4ccf-b224-8b0886d98116
-- title:
--   Theorem 1.2 — a polynomial-time $(1.9499+\varepsilon)$-pseudo-approximation for $k$-median opening $k + O(\log n/\varepsilon^2)$ centers
-- statement:
--   This is the pseudo-approximation half of the paper's better-than-2 approximation for $k$-median: by opening slightly more than $k$ centers one can beat the factor $2$ against the optimum with $k$ centers.
--
--   An instance of metric $k$-median consists of a set $D$ of $n$ clients, a nonempty set $F$ of facilities, distances $d$ on $D \cup F$ satisfying the triangle inequality, and an integer $k \ge 1$. For a nonempty $S \subseteq F$, $\mathrm{cost}(S) = \sum_{j \in D} \min_{i \in S} d(i,j)$, and $\mathrm{opt}$ is the minimum of $\mathrm{cost}(S)$ over nonempty $S \subseteq F$ with $|S| \le k$.
--
--   **Theorem.** There is an absolute constant $C$ such that for every $\varepsilon > 0$ there is a deterministic polynomial-time algorithm that, on every instance with rational distances, outputs a nonempty set $S \subseteq F$ with
--   $$|S| \le k + C\,\frac{\log n}{\varepsilon^2} \qquad\text{and}\qquad \mathrm{cost}(S) \le (1.9499 + \varepsilon)\cdot \mathrm{opt}.$$
--
--   The algorithm is a "smooth" (log-adaptive) implementation of the greedy facility-location algorithm with the modified bids $[\alpha - 1.224\,d]^+$; its guarantee comes from the $1.9499$-LMP approximation of Theorem 1.3. In the paper it is combined with the algorithm for stable instances (Theorem 1.4) to prove Theorem 1.1.
--
--   Differences from the source:
--   - encoding: "a polynomial-time algorithm" (no machine model named) → for each $\varepsilon$ one `Turing.TM2ComputableInPolyTime` multi-tape Turing machine with finite tape alphabets, reading the binary code of the instance and writing the indicator bit-list of $S$; the polynomial may depend on $\varepsilon$; reason: the paper names no model; same model as the published `BetterKMedian.LMPGreedy.theorem_1_3`.
--   - encoding: "$k + O(\log n/\varepsilon^2)$ centers" → one absolute constant $C$, chosen before $\varepsilon$ and the instance, with $|S| \le k + C\log n/\varepsilon^2$, where $n = |D|$ and $\log$ is the natural logarithm; reason: $O(\cdot)$ is an absolute constant; the paper sets $n$ to be the number of clients (§1). This is the reading of the authors' own Lean formalization (`BCFGJPSSV26.kMedian_pseudoApproximation`, https://github.com/raresbuhai/formalization-of-my-research/tree/main/BCFGJPSSV26). For $n \le 1$ the bound is $|S| \le k$.
--   - encoding: instances with real data → rational distances, written in binary; reason: a Turing machine receives finite input.
--   - reading: "metric distances on $D \cup F$" → a pseudometric on finitely many points, with $D$ and $F$ subsets that may overlap; reason: as in the published facility-location definitions for this paper.
--   - generalization: standing assumption (3), $1 \le d(i,j) \le \mathrm{poly}(|D|)$ (p. 5) → no such assumption; reason: (3) is a reduction step, not a restriction of the theorem.
--   - encoding: "cost at most $(1.9499+\varepsilon)\cdot\mathrm{opt}$" → $\mathrm{opt} = \mathrm{opt}_k$, the optimum over nonempty sets of at most $k$ facilities; the constant is the real `19499 / 10000`; reason: §2 definition; exact value.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/693.pdf, Theorem 1.2, printed p. 3 (PDF 5); §2, printed pp. 5–6 (PDF 7–8)

import Mathlib
import Definitions.Def_BetterKMedian_KMedian_Model

set_option autoImplicit false

namespace BetterKMedian.KMedian

theorem theorem_1_2 :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ (alg : RatInstance → List Bool)
        (P : Turing.TM2ComputableInPolyTime RatInstance.encode id alg),
        (∀ κ : P.tm.K, Finite (P.tm.Γ κ)) ∧
        ∀ I : RatInstance, ∃ S : Finset (Fin I.n),
          alg I = I.code S ∧ S ⊆ I.facilities ∧ S.Nonempty ∧
          (S.card : ℝ) ≤ (I.k : ℝ) + C * Real.log (I.clients.card : ℝ) / ε ^ 2 ∧
          I.cost S ≤ (19499 / 10000 + ε) * I.opt := by sorry

end BetterKMedian.KMedian
