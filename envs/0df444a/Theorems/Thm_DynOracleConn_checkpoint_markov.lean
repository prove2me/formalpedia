-- Prove2me | Theorems.Thm_DynOracleConn_checkpoint_markov
-- name    : DynOracleConn.checkpoint_markov
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:55.397137+00:00
-- url     : https://prove2.me/theorems/3654e729-60dc-411f-830e-bf7080f77d66
-- title:
--   §3.2.1, p.22 — a low-hit execution has $\mathbb P_\Phi[H_c\le B/2]\ge15/16$
-- statement:
--   Let $1\le B\le d/128$ and $\ell=\lfloor d/(64B)\rfloor$. Let $q_1,\dots,q_{8B}$ be distinct red intervals and let $W$ be a set of at most $B\ell/32$ slots, the slots hit by a low-hit execution. For uniform offsets $\Phi\in[\ell]^{8B}$, put $u_k$ at the $\phi_k$-th slot of the blue interval following red interval $q_k$. Then
--
--   $$\mathbb P_\Phi\big[\#\{k: u_k\in W\}\le B/2\big]\ge\frac{15}{16}.$$
--
--   **Formalization Note** The statement is for one fixed execution, with $W$ and the $q_k$ fixed.
--
--   Differences from the source:
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - encoding: probability over uniform (π, z), blocks or offsets → a count of outcomes; reason: the outcome spaces are finite and uniform; same statement
--   - generalization: one execution of the algorithm with H ≤ Bℓ/32 → any set W of at most Bℓ/32 slots and any distinct red intervals; reason: an execution supplies such W and q
--   - generalization: standing 10 ≤ B (§3.1, p.20) → 1 ≤ B; reason: the bound holds for 1 ≤ B and specializes to 10 ≤ B
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §3.2.1, p.22

import Mathlib
import Definitions.Def_DynOracleConn_Blocks

namespace DynOracleConn

/-- **§3.2.1, p.22 — a low-hit execution hits few checkpoints.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §3.2.1, p.22: "For each
k ∈ [8B], sample ϕ_k ∼ Unif([ℓ]) independently and uniformly at random … If t_k ∈ R_q, let u_k be the
ϕ_k-th slot of B_q. Call these points checkpoints. If H distinct slots are hit during the probes of
this block and H_c of them are checkpoints, then E_Φ[H_c] ≤ H/ℓ. Call an execution low-hit if
H ≤ Bℓ/32, and high-hit otherwise. For every low-hit execution, by Markov's inequality,
P_Φ[H_c ≤ B/2] ≥ 15/16."

For `1 ≤ B ≤ d/128`, distinct red intervals `q_0, …, q_{8B−1}` (among the first `32B`) and a set `W`
of at most `Bℓ/32` hit slots, at least `15/16` of the `ℓ^{8B}` offset vectors `Φ` put at most `B/2`
of the checkpoints `u_k = (2q_k + 1)ℓ + Φ_k` into `W`.

**Formalization Note.** 0-based: the `Φ_k`-th slot of blue interval `q_k` is `(2q_k+1)ℓ + Φ_k`. The
statement is for a fixed execution (fixed `W` and fixed red intervals); the paper's standing
`10 ≤ B` is not needed. -/
theorem checkpoint_markov {d B : ℕ} (hB : 1 ≤ B) (hBd : 128 * B ≤ d) (q : Fin (8 * B) → ℕ)
    (hq : Function.Injective q) (hq32 : ∀ k, q k < 32 * B) (W : Finset ℕ)
    (hW : (W.card : ℝ) ≤ (B : ℝ) * (ell d B : ℝ) / 32) :
    (15 / 16 : ℝ) * (ell d B : ℝ) ^ (8 * B) ≤
      (Set.ncard {Φ : Fin (8 * B) → Fin (ell d B) |
        ((Finset.univ.filter (fun k => checkpointAt d B (q k) (Φ k).val ∈ W)).card : ℝ) ≤
          (B : ℝ) / 2} : ℝ) := by sorry

end DynOracleConn
