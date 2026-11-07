-- Prove2me | Theorems.Thm_DynOracleConn_theorem_3_7
-- name    : DynOracleConn.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:15.268419+00:00
-- url     : https://prove2.me/theorems/e3219089-64a4-41fa-a6bf-61479d607c79
-- title:
--   Theorem 3.7, p.25 — every randomized PPHP algorithm has an input with $\mathbb P_{\mathcal A}[\text{correct}_{\text{total}}\wedge L_{\text{total}}\le c_Bc_Ld^3/B]\le1/3$
-- statement:
--   Let $c_L,\eta,c_B$ be constants for which Corollary 3.6's conclusion holds, and let $10\le B\le\eta d$ with $B\le d/128$. For every randomized PPHP stream algorithm $\mathcal A$ with at most $2^B$ states, there are an instance $X$ and a query sequence $\mathcal I$ of the length of Corollary 3.6 such that
--
--   $$\mathbb P_{\mathcal A}\Big[\mathrm{correct}_{\mathrm{total}}\ \wedge\ L_{\mathrm{total}}\le c_Bc_L\frac{d^3}{B}\Big]\le\frac13.$$
--
--   **Formalization Note** A randomized algorithm is a probability space of deterministic stream algorithms with one state type and measurable runs. The random tape is not charged as memory.
--
--   Differences from the source:
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - reading: c_B and c_L "according to Corollary 3.6 and Corollary 3.3" → for every c_L, η, c_B satisfying Corollary 3.6's conclusion (Cor36Holds); reason: the constants are chained; any witness of Corollary 3.6 instantiates it
--   - generalization: a randomized algorithm given a random tape → a probability space of deterministic stream algorithms; reason: a random tape is one such space; the proof fixes the tape
--   - encoding: probabilities over the random tape → measurable runs as a hypothesis; reason: a nondegeneracy condition: it makes the probability well defined on a general Ω
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 3.7, p.25

import Mathlib
import Definitions.Def_DynOracleConn_Blocks

namespace DynOracleConn

/-- **Theorem 3.7, p.25.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 3.7, p.25: "For every randomized algorithm 𝒜, there exists
an input such that P_𝒜[correct_total ∧ L_total ≤ c_B c_L d³/B] ≤ 1/3, where c_B and c_L are constants
chosen according to Corollary 3.6 and Corollary 3.3, respectively."

For constants `c_L, η, c_B` satisfying Corollary 3.6 (`Cor36Holds cL η cB`) and all `d, B` with
`10 ≤ B ≤ ηd` and `B ≤ d/128`: for every randomized PPHP stream algorithm with at most `2^B` states
and measurable runs there are an instance `X` and a query sequence `ℐ` of `numEpochs cB d B`
queries on which the algorithm answers all queries correctly with at most `c_B c_L d³/B` probes
with probability at most `1/3`.

**Formalization Note.** A randomized algorithm is a probability space of deterministic stream
algorithms with one state type (the random tape is not charged as memory). -/
theorem theorem_3_7 (cL η cB : ℝ) (h36 : Cor36Holds cL η cB) {d B : ℕ} (hB : 10 ≤ B)
    (hBd : 128 * B ≤ d) (hBη : (B : ℝ) ≤ η * d) {S : Type} [Fintype S]
    (hS : Fintype.card S ≤ 2 ^ B) (A : RandPPHPAlg d S) (hA : PPHPMeasurableRuns A) :
    ∃ (X : PPHPInst d) (ℐ : Fin (numEpochs cB d B) → Fin d),
      A.μ {ω | (A.alg ω).correctTotal X (List.ofFn ℐ) ∧
        ((A.alg ω).Ltotal X (List.ofFn ℐ) : ℝ) ≤ cB * cL * (d : ℝ) ^ 3 / B} ≤ 1 / 3 := by sorry

end DynOracleConn
