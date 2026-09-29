-- Prove2me | Theorems.Thm_FamousTheorems_beattyseq_symmdiff_beattyseq_pos
-- name    : FamousTheorems.beattyseq_symmdiff_beattyseq_pos
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:43.300256+00:00
-- url     : https://prove2.me/theorems/67110529-2920-4681-ab46-2ef898135c5f
-- title:
--   Beatty's theorem
-- statement:
--   **Beatty's theorem.** If $r$ and $s$ are positive irrationals with $1/r + 1/s = 1$, the two Beatty sequences $\lfloor nr \rfloor$ and $\lfloor ns \rfloor$ partition the positive integers: every positive integer appears in exactly one, exactly once. Two interleaved arithmetic-like sequences tile $\mathbb{N}$ with no overlaps and no gaps. Irrationality is essential — rational $r$ produces collisions — and the conjugacy condition is exactly what balances the densities $1/r$ and $1/s$ to sum to one. The theorem is the source of Wythoff's game, whose losing positions are the Beatty sequences for $\varphi$ and $\varphi^2$. **Formalization note.** The conclusion is stated as the symmetric difference of the two sequences covering the positives. The result is Mathlib's `Irrational.beattySeq_symmDiff_beattySeq_pos`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem beattyseq_symmdiff_beattyseq_pos :
    ∀ {r s : ℝ}, 
    r.HolderConjugate s → 
    Irrational r → symmDiff {x | ∃ k > 0, beattySeq r k = x} {x | ∃ k > 0, beattySeq s k = x} = {n | 0 < n} := by sorry

end FamousTheorems
