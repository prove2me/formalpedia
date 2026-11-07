-- Prove2me | Theorems.Thm_DynOracleConn_lemma_3_5
-- name    : DynOracleConn.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:04.797882+00:00
-- url     : https://prove2.me/theorems/373b2b36-be41-43cf-96d5-d2b0948ac633
-- title:
--   Lemma 3.5, p.24 — $\mathbb P_{\pi,z,I^t}[\text{correct}\wedge L<c_Ld^2]\le1/4$
-- statement:
--   Let $c_L,\eta$ be constants for which Corollary 3.3's conclusion holds, and let $10\le B\le\eta d$ and $B\le d/128$. For every advice map into at most $2^B$ strings and every block algorithm,
--
--   $$\mathbb P_{\pi,z,I^t}\big[\text{correct}\ \wedge\ L<c_Ld^2\big]\le\frac14,$$
--
--   where "correct" says that all $512B$ outputs of the block are right. A block answered correctly from $B$ bits of advice therefore needs $\Omega(d^2)$ probes with constant probability.
--
--   **Formalization Note** The advice depends on $(\pi,z)$ only, and the block is independent of them.
--
--   Differences from the source:
--   - encoding: probability over uniform (π, z), blocks or offsets → a count of outcomes; reason: the outcome spaces are finite and uniform; same statement
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - generalization: the algorithm processes a block online → a probe tree that sees the block in advance and returns all 512B outputs; reason: online processing is a special case, and §3 p.19 allows unlimited workspace within a block
--   - reading: c_L "according to Corollary 3.3" → for every c_L, η satisfying Corollary 3.3's conclusion (Cor33Holds); reason: the constants are chained; any witness of Corollary 3.3 instantiates it
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Lemma 3.5, p.24

import Mathlib
import Definitions.Def_DynOracleConn_Blocks

namespace DynOracleConn

/-- **Lemma 3.5, p.24.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), Lemma 3.5, p.24: "For each block, P_{π,z,Iᵗ}[correct ∧ L < c_L d²]
≤ 1/4 where c_L is according to Corollary 3.3."

For constants `c_L, η` satisfying Corollary 3.3 (`Cor33Holds cL η`) and all `d, B` with
`10 ≤ B ≤ ηd` and `B ≤ d/128`: for every advice map `M` into at most `2^B` strings and every block
algorithm `alg` (a probe tree for each advice and block of queries, returning the `512B` outputs),
the pairs `(X, Iᵗ)` on which all outputs are correct and fewer than `c_L d²` probes are made are at
most a quarter of the `d!·2^d·d^{512B}` pairs.

**Formalization Note.** The block algorithm may read the whole block `Iᵗ` before probing; an online
block algorithm is a special case. The advice depends on `X` only. -/
theorem lemma_3_5 (cL η : ℝ) (h33 : Cor33Holds cL η) {d B : ℕ} (hB : 10 ≤ B)
    (hBd : 128 * B ≤ d) (hBη : (B : ℝ) ≤ η * d) {Adv : Type} [Fintype Adv]
    (hAdv : Fintype.card Adv ≤ 2 ^ B) (M : PPHPInst d → Adv)
    (alg : Adv → (Fin (512 * B) → Fin d) → PPHPTree d (Fin (512 * B) → Bool)) :
    (Set.ncard {p : PPHPInst d × (Fin (512 * B) → Fin d) |
        BlockCorrect p.1 p.2 ((alg (M p.1) p.2).run (pOracle p.1)) ∧
        (((alg (M p.1) p.2).cost (pOracle p.1) : ℕ) : ℝ) < cL * (d : ℝ) ^ 2} : ℝ) ≤
      (1 / 4 : ℝ) * ((d.factorial : ℝ) * 2 ^ d * (d : ℝ) ^ (512 * B)) := by sorry

end DynOracleConn
