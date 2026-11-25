-- Prove2me | Theorems.Thm_DetDLP_lemma_4_4_coset_update_halving
-- name    : DetDLP.lemma_4_4_coset_update_halving
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T09:28:12.933665+00:00
-- url     : https://prove2.me/theorems/d19679c8-d82a-41c1-b927-ce412941f512
-- title:
--   Lemma 4.4: Deterministic Modular Affine-Coset Update and Halving
-- statement:
--   There exist a deterministic multitape Turing machine $M$ and a constant $K \in \mathbb{N}$ such that for all integers $M_{\mathrm{lab}} \ge 2$ and $N \ge 1$, every lower-triangular column-HNF modular lattice basis $B \in \mathbb{Z}^{N \times N}$ ($M_{\mathrm{lab}}\mathbb{Z}^N \subseteq B\mathbb{Z}^N$, $\det B \mid M_{\mathrm{lab}}^N$), every $x_0, a \in (\mathbb{Z}/M_{\mathrm{lab}}\mathbb{Z})^N$, and every $c_0 \in \mathbb{Z}/M_{\mathrm{lab}}\mathbb{Z}$ whose intersected coset $\mathcal{A}' = \{x \in \mathcal{A} : a^\top x = c_0\}$ is nonempty, setting $g_* = \gcd(M_{\mathrm{lab}}, |a^\top b_1|, \dots, |a^\top b_N|)$, there exist an updated representation $(x_0', B')$ of $\mathcal{A}'$ computable by $M$ in time and space $K(N + \lceil \log_2 M_{\mathrm{lab}} \rceil + 1)^K$ satisfying
--
--   $$|\mathcal{A}'| \cdot M_{\mathrm{lab}} = |\mathcal{A}| \cdot g_*,$$
--
--   and whenever $a^\top x_0 \neq c_0$ in $\mathbb{Z}/M_{\mathrm{lab}}\mathbb{Z}$, both $g_* < M_{\mathrm{lab}}$ and $2|\mathcal{A}'| \le |\mathcal{A}|$.
--
--   This exact modular lattice update handles composite moduli $M_{\mathrm{lab}} = p - 1$ deterministically and guarantees convergence in at most $\lceil N \log_2 M_{\mathrm{lab}} \rceil$ cuts.
--
--   **Formalization Note** All HNF entries are automatically bounded by $M_{\mathrm{lab}}$, so the input bit-length is $\mathrm{poly}(N, \log M_{\mathrm{lab}})$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.3, Lemma 4.4 (p. 17)

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem lemma_4_4_coset_update_halving :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
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
            RunsWithin M out
              (encodeCosetUpdateInput Mlab (fun i => (x0 i).val) B (fun i => (a i).val) c0.val)
              (encodeCosetRep (fun i => (x0' i).val) B')
              (polyBound K (N + bitLen Mlab))
              (polyBound K (N + bitLen Mlab)) ∧
            ((∑ i : Fin N, a i * x0 i ≠ c0) → gstar < Mlab ∧ 2 * Nat.card A' ≤ Nat.card A) := by
  sorry

end DetDLP
