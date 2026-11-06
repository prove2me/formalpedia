-- Prove2me | Theorems.Thm_FasterSFM_lemma_10
-- name    : FasterSFM.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:40.951368+00:00
-- url     : https://prove2.me/theorems/99b5c98f-6ec2-4998-ad5d-289513177713
-- title:
--   Lemma 10 — full-space and restricted inverse comparison
-- statement:
--   Let $J\in\mathbb R^{n\times N}$ have orthonormal columns spanning $S$.
--
--   1. For every positive definite $H\in\mathbb R^{n\times n}$ and every $b\in S$,
--   $$b^\top J(J^\top HJ)^{-1}J^\top b\ \le\ b^\top H^{-1}b .$$
--   2. For every cutting-plane body $P$ and $x\in\operatorname{int}P$, with $A_S=A_{\mathrm{fl}}(x)J$, one has $A_S^\top A_S=H_S:=J^\top H_{\mathrm{fl}}(x)J$, and for every $e\in\mathbb R^M$
--   $$\|A_S^\top e\|_{H_S^{-1}}\ \le\ \|e\|_2 .$$
--
--   Both comparisons are used to measure full-space quantities in the restricted norm, in Lemmas 11, 12 and 15.
--
--   Differences from the source:
--   - generalization: the current subspace S of block-constant vectors with its basis J = (ξ_C)_C (§5.1, p.16) → the column space of any J ∈ ℝ^{n×N} with JᵀJ = I; reason: the proof uses only that J has orthonormal columns; the block basis is an instance (reading R8)
--   - encoding: H_S at x → H_S = Jᵀ H_fl(x) J for the full-space point x; reason: the paper's H_S(y) at x = Jy; the lemma states it at any x ∈ int P
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 10, p.21

import Mathlib
import Definitions.Def_FasterSFM_Barrier

namespace FasterSFM

open Classical Matrix

/-- **Lemma 10** (Full-space and restricted inverse comparison), p.21.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 10, p.21.

"Let H ∈ ℝ^{n×n} be positive definite. For every b ∈ S, bᵀJ(JᵀHJ)⁻¹Jᵀb ≤ bᵀH⁻¹b. Moreover, at any
x ∈ int P put A_S = A_fl(x)J, so that A_SᵀA_S = H_S. Then for every vector e ∈ ℝ^M,
‖A_Sᵀe‖_{H_S⁻¹} ≤ ‖e‖₂."

**Formalization Note.** `S` is the column space of `J ∈ ℝ^{n×N}` with `JᵀJ = I` (reading R8: any
subspace). For a point `x ∈ int P` of the full space, `H_S = Jᵀ H_fl(x) J`; the identity
`A_SᵀA_S = H_S` is stated as a conjunct. The body is any body with its `2n` cube rows. -/
theorem lemma_10 {n N : ℕ} (J : Matrix (Fin n) (Fin N) ℝ) (hJ : Jᵀ * J = 1) :
    (∀ H : Matrix (Fin n) (Fin n) ℝ, H.PosDef → ∀ b ∈ colSpace J,
      b ⬝ᵥ ((J * (Jᵀ * H * J)⁻¹ * Jᵀ) *ᵥ b) ≤ b ⬝ᵥ (H⁻¹ *ᵥ b)) ∧
    (∀ (P : Body n) (x : Fin n → ℝ), P.Interior x →
      (P.Afl x * J)ᵀ * (P.Afl x * J) = Jᵀ * P.Hfl x * J ∧
      ∀ e : Row n P.k → ℝ,
        Real.sqrt (((P.Afl x * J)ᵀ *ᵥ e) ⬝ᵥ ((Jᵀ * P.Hfl x * J)⁻¹ *ᵥ ((P.Afl x * J)ᵀ *ᵥ e))) ≤
          Real.sqrt (∑ i, e i ^ 2)) := by sorry

end FasterSFM
