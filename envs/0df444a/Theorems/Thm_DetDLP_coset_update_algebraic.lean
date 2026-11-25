-- Prove2me | Theorems.Thm_DetDLP_coset_update_algebraic
-- name    : DetDLP.coset_update_algebraic
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:24:32.103709+00:00
-- url     : https://prove2.me/theorems/af97d0a2-6c40-4fbd-8555-d335f4132afd
-- title:
--   Hermite representative and exact index after a modular coset update
-- statement:
--   Let $A=x_0+B\mathbb Z^N\pmod m$, where $B$ is in column Hermite form and its lattice contains $m\mathbb Z^N$. Assume the section $A'=\{x\in A:a^Tx=c\}$ is nonempty. Put $d=\gcd(m,(\widetilde a^TB)_1,\ldots,(\widetilde a^TB)_N)$ using canonical integer lifts of the constraint coefficients. There exist $x_1$ and a lower triangular column Hermite basis $D$ with $m\mathbb Z^N\subseteq D\mathbb Z^N$ and $\det D\mid m^N$ such that
--   $$A'=x_1+D\mathbb Z^N\pmod m,\qquad |A'|m=|A|d.$$
--   If $a^Tx_0\ne c$, then $d<m$ and $2|A'|\le |A|$. This is the algebraic conclusion of Lemma 4.4, with no algorithmic hypothesis.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Lemma 4.4, algebraic conclusions.

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem coset_update_algebraic :
    ∀ (Mlab N : ℕ) [NeZero Mlab], 2 ≤ Mlab → 1 ≤ N →
        ∀ (x0 : Fin N → ZMod Mlab) (B : Matrix (Fin N) (Fin N) ℤ)
          (a : Fin N → ZMod Mlab) (c0 : ZMod Mlab),
          IsModularLatticeBasis Mlab B →
          let A := affineCoset Mlab x0 B
          let A' := {x ∈ A | ∑ i : Fin N, a i * x i = c0}
          A'.Nonempty →
          let gstar : ℕ :=
            Finset.univ.fold Nat.gcd Mlab
              (fun j : Fin N => Int.natAbs (∑ i : Fin N, ((a i).val : ℤ) * B i j))
          ∃ (x0' : Fin N → ZMod Mlab) (B' : Matrix (Fin N) (Fin N) ℤ),
            IsModularLatticeBasis Mlab B' ∧
            affineCoset Mlab x0' B' = A' ∧
            Nat.card A' * Mlab = Nat.card A * gstar ∧
            ((∑ i : Fin N, a i * x0 i ≠ c0) → gstar < Mlab ∧ 2 * Nat.card A' ≤ Nat.card A) := by sorry

end DetDLP
