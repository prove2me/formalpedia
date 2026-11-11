-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_theorem_1_1
-- name    : FlowSparsSchur.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:57.78743+00:00
-- url     : https://prove2.me/theorems/cebe0254-8727-4f00-acba-fdf630ce3175
-- title:
--   Theorem 1.1 — an O(log^{2.5} k)-quality flow sparsifier on the k terminals in Õ(m^{3/2} log 𝒰) time with high probability
-- statement:
--   There is a universal constant $C_q>0$ such that for every failure exponent $c\ge1$ there are one program $P$ of the randomized exact real RAM (rational literals, no `rpow`) and constants $C,K\in\mathbb N$ with the following property. For every connected capacitated multigraph $G$ on $\{0,\dots,n-1\}$ without self-loops, with $m$ edges and capacities $u(e)>0$, and every list $s$ of $k\ge2$ distinct terminals $S=\{s_0,\dots,s_{k-1}\}\subseteq V(G)$, with probability at least $1-n^{-c}$ over the fair coin tape the run of $P$ on the encoded input halts within
--   $$C\,m^{3/2}\log_2(2\mathcal U)\,\log_2(m+2)^K+C\qquad\Big(\mathcal U=\frac{\max_eu(e)}{\min_eu(e)}\Big)$$
--   steps, and its output is a capacitated graph $H$ with vertex set exactly $S$ (edges between distinct terminals, capacities $\ge0$) that is a $q$-flow sparsifier of $G$ for $S$ with $q=C_q(\log_2k)^{5/2}$:
--   $$G\overset{1}{\hookrightarrow}H\quad\text{and}\quad H\overset{q}{\hookrightarrow}G ,$$
--   for $S$-multicommodity demands with any number of commodities and load summed in absolute value over the commodities.
--
--   This is the paper's headline result: the first flow-sparsifier construction with polylogarithmic quality in time subquadratic in $m$.
--
--   **Formalization Note** The input is $(n,m,k,$ edge endpoints, terminals$)$ in integer memory and the capacities in real memory; the output is read from fixed cells (`Definitions.Def_FlowSparsSchur_Main_IO`). The conductance field of the input graph is unused. $n\ge2$ and $m\ge1$ follow from $k\ge2$ distinct terminals and connectivity.
--
--   Differences from the source:
--   - reading: "there is a randomized algorithm" → one program of the randomized real RAM `PNormReg_Machine` with rational literals and no `rpow` instruction, fixed before the instance (per c); reason: the paper names no machine; the algorithm uses only + − × ÷, √, comparisons and random bits.
--   - reading: Õ(m^{3/2} log 𝒰) time → at most C·m^{3/2}·log₂(2𝒰)·log₂(m+2)^K + C steps with C, K fixed before the instance; reason: Õ hides polylogarithmic factors, n ≤ m + 1 for a connected graph, and log₂(2𝒰) ≥ 1 avoids a vacuous bound at 𝒰 = 1.
--   - reading: "with high probability" → for every c ≥ 1, failure probability at most n^{−c} (outer measure of the failure set under the fair-coin tape), the event covering both the step bound and the sparsifier property; reason: the standard meaning; the paper runs Algorithm 1 with δ = 1/poly(n).
--   - reading: quality O(log^{2.5} k) → C_q·(log₂ k)^{5/2} with C_q universal, chosen before c; reason: the proof's quality 2(10α_avg + 2) does not depend on δ, so this stronger reading holds.
--   - generalization: S ⊂ V(G) → S ⊆ V(G); reason: S = V(G) is also covered and the statement specializes to proper subsets.
--   - encoding: graph G and terminals → edge list on {0, …, n − 1} with endpoints and capacities, terminals as an injective list; output H → a list of (i, j, κ) triples on fixed memory cells with κ ≥ 0, parallel edges not merged; reason: a program reads and writes memory, parallel capacities add for routing, and an edge of capacity 0 carries no flow, so it is the same as no edge (the source's graphs have capacities > 0).
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 1, Theorem 1.1

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Routing
import Definitions.Def_FlowSparsSchur_Main_IO

namespace FlowSparsSchur.Main

open PNormReg

/-- **Theorem 1.1** (p. 1). There is a universal `C_q > 0` such that for every failure exponent
`c ≥ 1` there are one admissible, `rpow`-free program `P` of the randomized real RAM and constants
`C, K ∈ ℕ` such that for every connected capacitated multigraph `G` on `{0, …, n − 1}` without
self-loops (`m` edges, capacities `u > 0`) and every list `s` of `k ≥ 2` distinct terminals, with
probability at least `1 − n^{−c}` over the fair coin tape, the run of `P` on the encoded input halts
within `C·m^{3/2}·log₂(2𝒰)·log₂(m+2)^K + C` steps and outputs a graph `H` on exactly the terminal set
`S` (edges between distinct terminals, capacities `≥ 0`) that is a `C_q (log₂ k)^{5/2}`-flow
sparsifier of `G` for `S`. The failure set is bounded in outer measure. -/
theorem theorem_1_1 :
    ∃ Cq : ℝ, 0 < Cq ∧
    ∀ c : ℝ, 1 ≤ c →
    ∃ (P : Program) (C K : ℕ), Admissible P ∧ NoRpow P ∧
    ∀ (n m k : ℕ) (G : CGraph (Fin n) (Fin m)) (s : Fin k → Fin n),
      2 ≤ k → Function.Injective s → G.NoLoops → G.PosCap → G.Connected →
      coinTape {ω : ℕ → Bool | ¬ ∃ t : ℕ,
          (t : ℝ) ≤ (C : ℝ) * (m : ℝ) ^ (3 / 2 : ℝ) * Real.logb 2 (2 * G.capRatio) *
              Real.logb 2 ((m : ℝ) + 2) ^ K + C ∧
          (run P (initState (inputInts n m k G s) (capList G)) ω t).halted = true ∧
          ∃ hS : OutOnTerminals (termSet s) (run P (initState (inputInts n m k G s) (capList G)) ω t),
            OutNoLoops (run P (initState (inputInts n m k G s) (capList G)) ω t) ∧
            (∀ i : ℕ, (i : ℤ) < outCount (run P (initState (inputInts n m k G s) (capList G)) ω t) →
              0 ≤ outWeight (run P (initState (inputInts n m k G s) (capList G)) ω t) i) ∧
            IsFlowSparsifier (Cq * Real.logb 2 (k : ℝ) ^ (5 / 2 : ℝ)) G (termSet s)
              (outCapGraph (termSet s)
                (run P (initState (inputInts n m k G s) (capList G)) ω t) hS)}
        ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end FlowSparsSchur.Main
