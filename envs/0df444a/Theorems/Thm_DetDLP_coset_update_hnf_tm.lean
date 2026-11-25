-- Prove2me | Theorems.Thm_DetDLP_coset_update_hnf_tm
-- name    : DetDLP.coset_update_hnf_tm
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T11:23:30.763815+00:00
-- url     : https://prove2.me/theorems/d039d2d7-dd69-4a4d-a3a8-519fe8c5052a
-- title:
--   Polynomial-Time Kannan–Bachem Column-HNF Coset-Update Machine
-- statement:
--   There exists a uniform deterministic multitape Turing machine running in $\mathrm{poly}(N, \log M_{\mathrm{lab}})$ time and space that, given a canonical modular lattice basis $(x_0, B)$ for a nonempty affine coset $\mathcal{A} \subseteq (\mathbb{Z}/M_{\mathrm{lab}}\mathbb{Z})^N$ and a linear congruence $a^\top x \equiv c_0 \pmod{M_{\mathrm{lab}}}$ with nonempty intersection $\mathcal{A}'$, computes an updated lower-triangular column-HNF modular lattice basis $(x_0', B')$ representing $\mathcal{A}'$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.3, Proof of Lemma 4.4(a) (p. 17)

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- Polynomial-time deterministic Kannan–Bachem HNF coset-update machine (Lemma 4.4(a), p. 17):
given canonical modular affine coset representation `(x0, B)` with `IsModularLatticeBasis Mlab B`
and a new congruence `aᵀ x ≡ c0 (mod Mlab)` whose intersection `A'` with `A` is nonempty,
computes in `poly(N, log Mlab)` time and space an updated lower-triangular column-HNF modular
lattice basis `(x0', B')` representing `A'`. -/
theorem coset_update_hnf_tm :
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
              (polyBound K (N + bitLen Mlab)) := by sorry

end DetDLP
