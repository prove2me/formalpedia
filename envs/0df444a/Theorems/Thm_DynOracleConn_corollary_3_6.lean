-- Prove2me | Theorems.Thm_DynOracleConn_corollary_3_6
-- name    : DynOracleConn.corollary_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:19.929488+00:00
-- url     : https://prove2.me/theorems/0c2a4801-1872-45a0-8f12-82cf7cc85316
-- title:
--   Corollary 3.6, p.25 — $\mathbb P_{\pi,z,\mathcal I}[\text{correct}_{\text{total}}\wedge L_{\text{total}}\le c_Bc_Ld^3/B]\le1/3$
-- statement:
--   Let $c_L>0$ and $\eta$ be constants for which Corollary 3.3's conclusion holds. There is a constant $c_B>0$ such that for all $10\le B\le\eta d$ with $B\le d/128$, every deterministic PPHP stream algorithm with at most $2^B$ states satisfies, on a stream of $4\lceil c_Bd/B\rceil$ blocks of $512B$ uniform queries,
--
--   $$\mathbb P_{\pi,z,\mathcal I}\Big[\mathrm{correct}_{\mathrm{total}}\ \wedge\ L_{\mathrm{total}}\le c_Bc_L\frac{d^3}{B}\Big]\le\frac13.$$
--
--   Here $\mathrm{correct}_{\mathrm{total}}$ says all outputs are correct, and $L_{\mathrm{total}}$ is the total number of probes.
--
--   **Formalization Note** The statement is `Cor36Holds cL η cB`.
--
--   Differences from the source:
--   - encoding: probability over uniform (π, z), blocks or offsets → a count of outcomes; reason: the outcome spaces are finite and uniform; same statement
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - reading: c_L "according to Corollary 3.3" → for every c_L > 0 and η satisfying Corollary 3.3's conclusion (Cor33Holds; Corollary 3.3 supplies c_L > 0); reason: the constants are chained; any witness of Corollary 3.3 instantiates it
--   - reading: "Assume there are 4c_Bd/B blocks", a count that need not be an integer → 4⌈c_B d/B⌉ blocks; reason: it is the integer multiple of 4 that keeps the Markov step at exactly 1/3 and the proof otherwise unchanged; ⌊·⌋ would give slightly more than 1/3
--   - encoding: B bits of memory persisting between blocks → state type S with at most 2^B elements; reason: same memory, up to relabeling
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Corollary 3.6, p.25

import Mathlib
import Definitions.Def_DynOracleConn_Blocks

namespace DynOracleConn

/-- **Corollary 3.6, p.25 (deterministic version).** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), Corollary 3.6, p.25: "There exists
constant c_B > 0 such that P_{π,z,ℐ}[correct_total ∧ L_total ≤ c_B c_L d³/B] ≤ 1/3, where c_L is a
constant chosen according to Corollary 3.3, correct_total is the event of output of the algorithm
being correct for all of the blocks, and L_total is the total number of probes done by the
algorithm (on all of the blocks altogether)."

For constants `c_L > 0, η` satisfying Corollary 3.3 there is `c_B > 0` such that, for all `d, B` with
`10 ≤ B ≤ ηd` and `B ≤ d/128`, every deterministic PPHP stream algorithm with at most `2^B` states
answers all `4⌈c_B d/B⌉·512B` uniform queries correctly with at most `c_B c_L d³/B` probes on at
most a third of the inputs `(π, z, ℐ)` (`Cor36Holds cL η cB`).

**Formalization Note.** The proof's "4c_B d/B blocks" is `4⌈c_B d/B⌉` blocks (`numEpochs`). -/
theorem corollary_3_6 (cL η : ℝ) (hcL : 0 < cL) (h33 : Cor33Holds cL η) :
    ∃ cB : ℝ, 0 < cB ∧ Cor36Holds cL η cB := by sorry

end DynOracleConn
