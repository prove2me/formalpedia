-- Prove2me | Theorems.Thm_DynOracleConn_lemma_3_4
-- name    : DynOracleConn.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:58.845173+00:00
-- url     : https://prove2.me/theorems/b2dca81f-1019-4221-b5e4-49f66c3e611c
-- title:
--   Lemma 3.4, p.23 — $\mathbb P_{\pi,z,\Phi}[\mathcal E\wedge Y\text{-correct}\wedge H_c\le B/2]\le2^{-30}$
-- statement:
--   Let $10\le B\le d/128$. For every fixed block $I^t$ and every algorithm receiving a $B$-bit advice $\mathcal M(\pi,z)$ and probing $P_X$,
--
--   $$\mathbb P_{\pi,z,\Phi}\big[\mathcal E\ \wedge\ Y\text{-correct}\ \wedge\ H_c\le B/2\big]\le2^{-30},$$
--
--   where $Y$-correct says that each $Y_k$ is obtained correctly from the outputs, for all $k\in[8B]$, and $H_c$ is the number of hit checkpoints. Together with Corollary 3.3, it says that correct answers need many hits.
--
--   **Formalization Note** The offsets $\Phi$ are for analysis only and the algorithm does not see them. $10\le B$ is the standing assumption of §3.1, p.20, and $B\le d/128$ that of §3.2.1, p.21.
--
--   Differences from the source:
--   - encoding: probability over uniform (π, z), blocks or offsets → a count of outcomes; reason: the outcome spaces are finite and uniform; same statement
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - generalization: the algorithm processes a block online → a probe tree that sees the block in advance and returns all 512B outputs; reason: online processing is a special case, and §3 p.19 allows unlimited workspace within a block
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Lemma 3.4, p.23

import Mathlib
import Definitions.Def_DynOracleConn_Blocks

namespace DynOracleConn

/-- **Lemma 3.4, p.23.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), Lemma 3.4, p.23: "For every fixed block Iᵗ,
P_{π,z,Φ}[ℰ ∧ (Y-correct) ∧ H_c ≤ B/2] ≤ 2^{−30}, where Y-correct is the event that Y_k is calculated
correctly from the output (for all k ∈ [8B])."

Under the standing assumptions `10 ≤ B` and `B ≤ d/128`, for every fixed block `I`, every advice map
`M` into at most `2^B` strings and every block algorithm `alg` (a probe tree for each advice, whose
leaf is the vector of the block's `512B` outputs), the triples `(π, z, Φ)` on which ℰ holds, the
outputs are Y-correct and at most `B/2` checkpoints are hit are at most a `2^{−30}` fraction of
the `d!·2^d·ℓ^{8B}` triples.

**Formalization Note.** `Φ : Fin (8B) → Fin ℓ` are the checkpoint offsets; the hit slots are those
of the run of `alg (M X)` on `P_X`. -/
theorem lemma_3_4 {d B : ℕ} (hB : 10 ≤ B) (hBd : 128 * B ≤ d) (I : Fin (512 * B) → Fin d)
    {Adv : Type} [Fintype Adv] (hAdv : Fintype.card Adv ≤ 2 ^ B) (M : PPHPInst d → Adv)
    (alg : Adv → PPHPTree d (Fin (512 * B) → Bool)) :
    (Set.ncard {p : PPHPInst d × (Fin (8 * B) → Fin (ell d B)) |
        EventE d B p.1.1 I ∧ YCorrect d B p.1 I ((alg (M p.1)).run (pOracle p.1)) ∧
        (numHitCheckpoints d B p.1.1 I p.2 (hitSlots (alg (M p.1)) p.1) : ℝ) ≤ (B : ℝ) / 2} : ℝ) ≤
      (1 / 2 ^ 30 : ℝ) * ((d.factorial : ℝ) * 2 ^ d * (ell d B : ℝ) ^ (8 * B)) := by sorry

end DynOracleConn
