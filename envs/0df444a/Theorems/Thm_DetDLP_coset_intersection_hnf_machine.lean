-- Prove2me | Theorems.Thm_DetDLP_coset_intersection_hnf_machine
-- name    : DetDLP.coset_intersection_hnf_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:35:11.93811+00:00
-- url     : https://prove2.me/theorems/81cbced8-3450-4445-8f9b-e01c77cc6342
-- title:
--   Polynomial-time Hermite normal form update for a modular affine lattice
-- statement:
--   Let $M\ge 2$, $N\ge 1$, and let an affine coset in $(\mathbb Z/M\mathbb Z)^N$ be given by a representative $x_0$ and a column Hermite normal form basis $B$ for an integer lattice containing $M\mathbb Z^N$. For a row $a$ and a residue $c$, suppose the section $A'=\{x\in x_0+\operatorname{im}(B)\bmod M:a^Tx=c\}$ is nonempty. A single deterministic multitape Turing machine outputs a representative $x'_0$ and a column Hermite normal form basis $B'$ for $A'$, with the required lattice containment and determinant divisibility. The time and space are polynomial in $N+\lceil\log_2 M\rceil$ for the specified binary encodings. This is the computational construction in part (a) of Lemma 4.4.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Lemma 4.4(a), Section 4.2.

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem coset_intersection_hnf_machine :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ (Mlab N : ℕ) [NeZero Mlab], 2 ≤ Mlab → 1 ≤ N →
        ∀ (x0 : Fin N → ZMod Mlab) (B : Matrix (Fin N) (Fin N) ℤ)
          (a : Fin N → ZMod Mlab) (c0 : ZMod Mlab),
          IsModularLatticeBasis Mlab B →
          let A := affineCoset Mlab x0 B
          let A' := {x ∈ A | ∑ i : Fin N, a i * x i = c0}
          A'.Nonempty →
          ∃ (x0' : Fin N → ZMod Mlab) (B' : Matrix (Fin N) (Fin N) ℤ),
            IsModularLatticeBasis Mlab B' ∧
            affineCoset Mlab x0' B' = A' ∧
            RunsWithin M out
              (encodeCosetUpdateInput Mlab (fun i => (x0 i).val) B (fun i => (a i).val) c0.val)
              (encodeCosetRep (fun i => (x0' i).val) B')
              (polyBound K (N + bitLen Mlab))
              (polyBound K (N + bitLen Mlab)) := by
  sorry

end DetDLP
