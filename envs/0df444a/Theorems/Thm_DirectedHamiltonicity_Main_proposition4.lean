-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_proposition4
-- name    : DirectedHamiltonicity.Main.proposition4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:43.953896+00:00
-- url     : https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66
-- title:
--   Proposition 4 — weighted Hamiltonian-path parity in $(2-2^{-d})^n\,\mathrm{poly}(n,W)$ time with success $\ge5/6$
-- statement:
--   There is one fixed randomized algorithm (a program of the log-cost RAM with fair coins) and constants $C>0$, $k$ such that the following holds. Let $d\ge1$ be an integer and let $H$ be an $n$-vertex directed multigraph with $m$ arcs and integer arc weights in $\{0,\dots,W\}$, such that the arcs entering each vertex have at most $d$ distinct weights. Given distinct vertices $s,t$ and an integer $B$ (encoded as input; $d$ and $W$ are not part of the input):
--
--   1. every run, for every coin string, halts with a one-bit output after total cost at most
--   $$T=C\,(2-2^{-d})^n\,(n+m+W+1)^k;$$
--   2. for uniformly random coins of any length $L\ge T$, the output equals the parity of the number of Hamiltonian paths from $s$ to $t$ of total weight $B$ with probability at least $5/6$.
--
--   The input multigraph may contain loops, arcs entering $s$, arcs leaving $t$ and parallel arcs of equal weight; $W=0$, $d=1$ and every integer $B$ (including $B<0$ and $B>(n-1)W$, where the parity is $0$) are allowed. When $m$ is polynomial in $n$, $T$ is $(2-2^{-d})^n\,\mathrm{poly}(n,W)$, the source's bound.
--
--   Differences from the source:
--   - generalization: H has polynomially many arcs; running time (2 − 2^{−d})^n poly(n, W) → any number m of arcs; total cost at most C(2 − 2^{−d})^n (n + m + W + 1)^k with C, k independent of the input and of d; reason: for m ≤ poly(n) the bound is (2 − 2^{−d})^n poly(n, W), the source statement
--   - reading: a randomized algorithm correctly computes the parity with probability at least 5/6; its running time is … → one fixed program of the published log-cost RAM (TargetedSamplers.Program); every run on every coin string halts with a one-bit output within the time bound; for uniform coin strings of every length L ≥ the time bound the output is the parity with probability ≥ 5/6; reason: the source fixes no machine model; the log-cost RAM charges every access and arithmetic step its bit length and allows exponential memory, and is polynomially equivalent to the usual RAM; the time bound is read as a worst-case bound over all coin outcomes
--   - encoding: an n-vertex multigraph H with weights, vertices s, t and integer B given as input → vertices Fin n, arcs Fin m with tail, head, w : Fin m → ℕ, encoded by encodeParityInstance as a bit string; the parity is Odd (weightedPathCount); reason: a standard binary encoding of the same instance
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.5 / printed p.4, Proposition 4 (repeated PDF p.7 / printed p.6; proof PDF pp.8–11 / printed pp.7–10)

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_Graphs
import Definitions.Def_DirectedHamiltonicity_Main_DetSum
import Definitions.Def_DirectedHamiltonicity_Main_Algorithms

namespace DirectedHamiltonicity.Main

open Multidigraph

/-- Proposition 4, PDF p.5 / printed p.4 (repeated PDF p.7; proof PDF pp.8–11). There is one fixed
randomized program `P` of the log-cost RAM and constants `C > 0`, `k` such that for every integer
`d ≥ 1`, every directed multigraph `H` on `n` vertices with `m` labelled arcs and integer arc weights
in `{0, …, W}` in which the arcs entering each vertex have at most `d` distinct weights, all distinct
`s, t` and every integer `B`, on the encoded input:

1. every run, for every coin string, halts with a one-bit output after a total cost of at most
   `T = C (2 − 2^{−d})^n (n + m + W + 1)^k`;
2. with uniformly random coins of any length `L ≥ T`, the output is the parity of the number of
   Hamiltonian paths from `s` to `t` of total weight `B` with probability at least `5/6`. -/
theorem proposition4 :
    ∃ (P : TargetedSamplers.Program) (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (n m W : ℕ) (tail head : Fin m → Fin n) (w : Fin m → ℕ),
        (∀ e, w e ≤ W) →
        (∀ v, (Multidigraph.incomingWeights
          (⟨tail, head⟩ : Multidigraph (Fin n) (Fin m)) w v).card ≤ d) →
        ∀ (s t : Fin n), s ≠ t → ∀ B : ℤ,
          (∀ coins : List Bool, ∃ (cost : ℕ) (b : Bool),
            P.RunsIn (runTapes (encodeParityInstance n m tail head w s t B) coins) cost (some [b]) ∧
            (cost : ℝ) ≤ C * (2 - (1 / 2 : ℝ) ^ d) ^ n * ((n + m + W + 1 : ℕ) : ℝ) ^ k) ∧
          (∀ L : ℕ, C * (2 - (1 / 2 : ℝ) ^ d) ^ n * ((n + m + W + 1 : ℕ) : ℝ) ^ k ≤ L →
            (5 / 6 : ℝ) ≤ outputProb P (encodeParityInstance n m tail head w s t B) L
              [decide (Odd
                (Multidigraph.weightedPathCount
                  (⟨tail, head⟩ : Multidigraph (Fin n) (Fin m)) w s t B))]) := by sorry

end DirectedHamiltonicity.Main
