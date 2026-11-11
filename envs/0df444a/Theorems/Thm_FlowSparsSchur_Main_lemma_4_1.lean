-- Prove2me | Theorems.Thm_FlowSparsSchur_Main_lemma_4_1
-- name    : FlowSparsSchur.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:24:49.498047+00:00
-- url     : https://prove2.me/theorems/c2c42278-9691-44a1-88d0-9551fb9fd23e
-- title:
--   Lemma 4.1 ([DKPRS17]) — approximate Schur complements in Õ(m + n log^{-2} ξ) time with O(k log^{-2}(ξ) log(n/δ)) edges, w.p. 1 − δ
-- statement:
--   Let $G$ be a connected graph on $\{0,\dots,n-1\}$ without self-loops, with $m$ edges and conductances $c(G)>0$, let $S$ be a set of $k\ge2$ terminals, $\xi\in(1,1.5)$ an accuracy parameter and $\delta$ a failure probability. Lemma 4.1 (cited from Durfee, Kyng, Peebles, Rao, Sachdeva 2017) asserts an algorithm $\mathrm{GetApproxSC}(G,S,\xi,\delta)$ that, with probability $1-\delta$, runs in $\widetilde O(m+n\log^{-2}\xi)$ time and returns a graph $H$ on $S$ with $|E(H)|=O(k\log^{-2}(\xi)\log(n/\delta))$ and
--   $$\xi^{-1}L_{\mathrm{Schur}(G,S)}\preceq L_H\preceq\xi L_{\mathrm{Schur}(G,S)} .$$
--
--   Formally: there is $C_E>0$ such that for every $c\ge1$ there are one admissible, rpow-free program $P$ and $C,K\in\mathbb N$ such that for every instance with $n^{-c}\le\delta<1$, the set of coin tapes on which $P$ fails to halt within $C(m+n/\ln^2\xi)\log_2(m+2)^K+C$ steps with an output graph $H$ on $S$ (edges between distinct terminals, conductances $>0$) satisfying $|E(H)|\le C_E\,k\ln^{-2}(\xi)\ln(n/\delta)$ and the spectral bound has outer measure at most $\delta$.
--
--   Lemma 4.1 is the subroutine called in every iteration of Algorithm 1, and its running time dominates one iteration.
--
--   **Formalization Note** The input is $(n,m,k,$ edges, terminals$)$ in integer memory and the conductances followed by $\xi,\delta$ in real memory (`Definitions.Def_FlowSparsSchur_Main_IO`).
--
--   Differences from the source:
--   - reading: "there exists an algorithm" → a program of the randomized real RAM `PNormReg_Machine`, with rational literals only and no `rpow` instruction; reason: the paper names no machine.
--   - reading: δ ∈ (1/poly(n), 1) → for every c ≥ 1, every δ with n^{−c} ≤ δ < 1, the program and C, K depending on c; reason: 1/poly(n) is a polynomial lower bound fixed before the instance.
--   - reading: Õ(m + n log^{−2} ξ) time → C·(m + n/ln²ξ)·log₂(m+2)^K + C steps, C, K fixed before the instance; reason: Õ hides polylogarithmic factors and n ≤ m + 1 for a connected graph.
--   - reading: |E(H)| = O(k log^{−2}(ξ) log(n/δ)) → ≤ C_E·k·ln^{−2}(ξ)·ln(n/δ) with C_E universal (quantified before c); reason: the bound shows its δ-dependence explicitly, so its constant does not depend on c.
--   - encoding: "with probability 1 − δ" → the failure set has outer measure ≤ δ under the fair-coin tape; reason: an outer-measure bound needs no measurability argument and implies the probability bound.
--   - encoding: input graph and output graph as edge lists in fixed memory cells, terminals as an injective list; reason: a program reads and writes memory.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), p. 15, Lemma 4.1

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_IO

namespace FlowSparsSchur.Main

open PNormReg

/-- **Lemma 4.1** ([DKPRS17], p. 15). There is a universal `C_E > 0` such that for every exponent
`c ≥ 1` there are one admissible, `rpow`-free program `P` (the algorithm `GetApproxSC`) and constants
`C, K ∈ ℕ` such that for every connected multigraph `G` on `{0, …, n − 1}` without self-loops, with
conductances `c(G) > 0`, every list `s` of `k ≥ 2` distinct terminals, every `ξ ∈ (1, 1.5)` and every
`δ ∈ [n^{−c}, 1)`, with probability at least `1 − δ` over the coin tape the run on the encoded input
`(G, S; ξ, δ)` halts within `C·(m + n·log^{−2} ξ)·log₂(m+2)^K + C` steps and returns a graph `H` on `S`
(edges between distinct terminals, conductances `> 0`) with `|E(H)| ≤ C_E·k·log^{−2}(ξ)·log(n/δ)` and
`ξ⁻¹ L_{Schur(G,S)} ⪯ L_H ⪯ ξ L_{Schur(G,S)}`. -/
theorem lemma_4_1 :
    ∃ CE : ℝ, 0 < CE ∧
    ∀ c : ℝ, 1 ≤ c →
    ∃ (P : Program) (C K : ℕ), Admissible P ∧ NoRpow P ∧
    ∀ (n m k : ℕ) (G : CGraph (Fin n) (Fin m)) (s : Fin k → Fin n) (ξ δ : ℝ),
      2 ≤ k → Function.Injective s → G.IsCondGraph →
      1 < ξ → ξ < 3 / 2 → (n : ℝ) ^ (-c) ≤ δ → δ < 1 →
      coinTape {ω : ℕ → Bool | ¬ ∃ t : ℕ,
          (t : ℝ) ≤ (C : ℝ) * ((m : ℝ) + (n : ℝ) / Real.log ξ ^ 2) *
              Real.logb 2 ((m : ℝ) + 2) ^ K + C ∧
          (run P (initState (inputInts n m k G s) (condList G ++ [ξ, δ])) ω t).halted = true ∧
          ∃ hS : OutOnTerminals (termSet s)
              (run P (initState (inputInts n m k G s) (condList G ++ [ξ, δ])) ω t),
            OutNoLoops (run P (initState (inputInts n m k G s) (condList G ++ [ξ, δ])) ω t) ∧
            (∀ i : ℕ, (i : ℤ) <
                outCount (run P (initState (inputInts n m k G s) (condList G ++ [ξ, δ])) ω t) →
              0 < outWeight (run P (initState (inputInts n m k G s) (condList G ++ [ξ, δ])) ω t) i) ∧
            (outCount (run P (initState (inputInts n m k G s) (condList G ++ [ξ, δ])) ω t) : ℝ) ≤
              CE * (k : ℝ) / Real.log ξ ^ 2 * Real.log ((n : ℝ) / δ) ∧
            SpecApprox ξ
              (outCondGraph (termSet s)
                (run P (initState (inputInts n m k G s) (condList G ++ [ξ, δ])) ω t) hS).lap
              (schurLap G (termSet s))}
        ≤ ENNReal.ofReal δ := by sorry

end FlowSparsSchur.Main
