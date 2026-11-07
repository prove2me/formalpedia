-- Prove2me | Theorems.Thm_BFAlmostLinear_theorem_1_1
-- name    : BFAlmostLinear.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:39:25.478376+00:00
-- url     : https://prove2.me/theorems/608e655e-8e07-43e0-89d4-579965bf11c5
-- title:
--   Theorem 1.1 — Las Vegas single-source shortest paths with real weights in $m^{1+o(1)}$ time whp
-- statement:
--   There is a program $P$ of the mission's word/real RAM with fair coins and a function $g$ with $g(k)\to0$ such that for every $C>0$ there is $K>0$ with the following property. For every directed multigraph $G$ with $n$ vertices and $m$ arcs, every weighting $w:E\to\mathbb R$ of any sign and every source $s$, run on the input $(G,w,s)$ with word bound $(m+n+2)^c$:
--
--   1. **(Las Vegas.)** On every coin tape, if $P$ halts, its output is correct: either a closed walk of negative weight whose start is reachable from $s$, or (when no such walk exists) the exact distance $d(s,v)$ of every reachable vertex $v$ with a shortest-path tree, and a flag for each unreachable vertex.
--   2. **(Time.)** The set of coin tapes on which $P$ has not halted within $K\,(m+2)^{1+g(m+2)}$ steps has outer measure at most $(m+2)^{-C}$.
--
--   There is no hypothesis on negative cycles, connectivity, $m\ge n$, or the size or integrality of the weights.
--
--   This is the paper's main result: real-weighted single-source shortest paths in almost-linear time, improving on the $\tilde O(mn^{8/9})$ line of algorithms.
--
--   **Formalization Note** One program and one $g$ serve every $C$. The output specification is `IsSSSPOutput`; the machine is `Machine.Program`. Memory starts at $0$, so $n$ enters only through the input and the word bound.
--
--   Differences from the source:
--   - reading: "a (Las Vegas) randomized algorithm" → one program of the word/real RAM with fair coins (real $+$, $-$, comparisons and literal $0$ only; integer words of size polynomial in the input), correct on every tape on which it halts; reason: the paper names no machine (`paper.md` decisions 2, 6).
--   - reading: "for single-source shortest paths" → the output is a certified negative closed walk reachable from $s$, or exact distances with a shortest-path tree; reason: the theorem names no output; Lemma 4.2 "reports a negative cycle" (p.13) and the proof "recover[s] the shortest paths" (p.12).
--   - encoding: $m^{1+o(1)}$ → $K(m+2)^{1+g(m+2)}$ with $g\to0$ chosen before $C$; reason: at $m=0$ the printed bound is $0$ while a program runs at least one step; for $m\ge2$ the forms agree.
--   - reading: probability $\ge1-1/n^C$ → failure outer measure $\le(m+2)^{-C}$; reason: the time bound is in $m$ alone and the proof assumes $n\le\tilde O(m_0)$ (p.27); in that regime this implies the printed bound after changing $C$, and the unreachable part of a graph with $n\gg m$ costs nothing.
--   - encoding: "with high probability" → outer measure of the bad tapes; reason: avoids a measurability side condition.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Theorem 1.1, p.1, footnotes 1–2, p.1; §1.1, p.2

import Mathlib
import Definitions.Def_BFAlmostLinear_IsSSSPOutput

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime Filter Topology

/-- **Theorem 1.1**, p.1. "There is a (Las Vegas) randomized algorithm for single-source shortest paths on
real-weighted directed graphs which runs in m^{1+o(1)} time, with high probability." Footnote 2: "With high
probability means with probability at least 1 − 1/n^C for arbitrarily large constant C > 0."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Theorem 1.1, p.1.

**Formalization Note.**
* There is one program `P` and one `g → 0`, before every `C > 0`, then `K`, then the instance: every `n`, `m`,
  multigraph, real `w` of any sign, and source. There is no hypothesis on negative cycles, connectivity,
  `m ≥ n`, or the size or integrality of weights.
* **Las Vegas.** On every tape on which it halts, the output is correct. The time bound `K (m+2)^{1+g(m+2)}`
  fails on a set of tapes of outer measure at most `(m+2)^{−C}`; a stuck state never halts.
* `m + 2`, in the time and in the failure probability alike: at `m = 0` the printed `m^{1+o(1)}` is `0` and a
  program runs at least one step. The printed failure is `1/n^C`, and the proof assumes `n ≤ Õ(m₀)`, p.27. In
  that regime this bound implies the printed one, up to changing `C`.
* The machine is `Machine.Program`, with word bound `(m + n + 2)^c`. Memory starts at `0`, so `n` appears only in
  the word bound and in the input. The output is `IsSSSPOutput`. -/
theorem theorem_1_1 :
    ∃ (P : Machine.Program) (g : ℕ → ℝ), Tendsto g atTop (𝓝 0) ∧
      ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧
        ∀ (n m : ℕ) (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (s : Fin n),
          let W := Machine.wordBound P (m + n + 2)
          let σ₀ := ssspInit G w (s : ℕ)
          (∀ (τ : ℕ → Bool) (T : ℕ), Machine.HaltsWithin P W τ σ₀ T →
            IsSSSPOutput G w s (Machine.run P W τ σ₀ T)) ∧
          Machine.coinTape {τ | ¬ Machine.HaltsWithin P W τ σ₀
              ⌈K * ((m : ℝ) + 2) ^ (1 + g (m + 2))⌉₊} ≤
            ENNReal.ofReal (((m : ℝ) + 2) ^ (-C)) := by sorry

end BFAlmostLinear
