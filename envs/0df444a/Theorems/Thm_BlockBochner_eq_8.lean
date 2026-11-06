-- Prove2me | Theorems.Thm_BlockBochner_eq_8
-- name    : BlockBochner.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:38:40.82995+00:00
-- url     : https://prove2.me/theorems/e2fae38f-f477-4a33-8765-39290bf3d426
-- title:
--   Eq. (8) — outer block bound $\|(B^{-1}_{RR})_{k\ell}\|\le(M^{-1}_{RR})_{k\ell}$
-- statement:
--   Let $H$ be a real Hilbert space, $W_1,\dots,W_n$ closed subspaces with orthogonal projections $P_i$, $P_{ij}$ the projection onto $W_i\cap W_j$, and $S=(s_{ij})$ a real symmetric matrix with non-negative entries, zero diagonal and $\lambda_{\max}(S)<1$ such that $\|P_iP_j-P_{ij}\|\le s_{ij}$ for all $i\ne j$. Let $M=I-S$ and let $B$ be the Bochner operator on $H_1=\bigoplus_iW_i$.
--   For $R\subseteq[n]$ let $B_{RR}$ be the compression of $B$ to $\bigoplus_{i\in R}W_i$ and $M_{RR}=I-S_{RR}$. Then for all $k,\ell\in R$ the $W_\ell\to W_k$ block of $B_{RR}^{-1}$ satisfies
--   $$\|(B^{-1}_{RR})_{k\ell}\|\le(M^{-1}_{RR})_{k\ell}.\tag{8}$$
--
--   This entrywise domination is what controls the Schur complement $\tilde B$ by the Schur complement $C$ of $M$.
--
--   **Formalization Note** The block norm bound is written pointwise: $\|(B_{RR}^{-1}z)_k\|\le(M_{RR}^{-1})_{k\ell}\|z_\ell\|$ for every $z\in\bigoplus_{i\in R}W_i$ supported on the coordinate $\ell$.
--
--   Differences from the source:
--   - generalization: R = [n] ∖ T → any R ⊆ [n]; reason: the proof of (8) uses no property of R; the source's R is an instance
--   - encoding: ‖(B⁻¹_RR)_kℓ‖ ≤ (M⁻¹_RR)_kℓ (operator norm of a block) → ‖(B_RR⁻¹ z)_k‖ ≤ (M_RR⁻¹)_kℓ ‖z_ℓ‖ for z supported on ℓ; reason: equivalent, since (M_RR⁻¹)_kℓ ≥ 0 (the source's Neumann series)
--   - reading: B⁻¹_RR → (B_RR)⁻¹, the inverse of the compression of B to ⊕_{i∈R} W_i; reason: the proof on p.24 fixes y, z with B_RR y = z and sets y = B⁻¹_RR z, and M⁻¹_RR is written (I − S_RR)⁻¹ on the same page
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.3, Eq. (8), p.24

import Mathlib
import Definitions.Def_BlockBochner_bochnerOp
import Definitions.Def_BlockBochner_IsAdmissible
import Definitions.Def_BlockBochner_coordSub
import Definitions.Def_BlockBochner_blk

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Eq. (8), outer block bound on `B⁻¹`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.3, Eq. (8), p.24:
`‖(B_{RR}⁻¹)_{kℓ}‖ ≤ (M_{RR}⁻¹)_{kℓ}` for all blocks `k, ℓ ∈ R`, where `B_{RR}` is the compression of
the Bochner operator to `⊕_{i∈R} W_i` and `M_{RR}⁻¹ = (I − S_{RR})⁻¹`.

Setting of Sec. 3.2 (p.21): `H` a real Hilbert space, `W₁, …, W_n` closed subspaces with orthogonal
projections `P_i`, `P_{ij}` the projection onto `W_i ∩ W_j`, and `S` a real symmetric matrix with
non-negative entries, zero diagonal and `λ_max(S) < 1` such that `‖P_i P_j − P_{ij}‖ ≤ s_{ij}` for all
`i ≠ j`; `M = I − S`.

**Formalization Note** Stated for every `R ⊆ [n]` (the source applies it to `R = [n] ∖ T`). The
operator-norm bound on the block `W_ℓ → W_k` is written pointwise: for every `z ∈ ⊕_{i∈R} W_i`
supported on the coordinate `ℓ`, `‖(B_{RR}⁻¹ z)_k‖ ≤ (M_{RR}⁻¹)_{kℓ} ‖z_ℓ‖`; the entries of `M_{RR}⁻¹`
are non-negative, so this is equivalent. `B_{RR}⁻¹` is `Ring.inverse` of the compression `blk`, and
`M_{RR}⁻¹` is the matrix inverse of the principal submatrix. -/
theorem eq_8 {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsAdmissible S)
    (hang : ∀ i j, i ≠ j → ‖(W i : Submodule ℝ H).starProjection ∘L (W j : Submodule ℝ H).starProjection -
      ((W i ⊓ W j : ClosedSubmodule ℝ H) : Submodule ℝ H).starProjection‖ ≤ S i j)
    (R : Finset (Fin n)) (k l : Fin n) (hk : k ∈ R) (hl : l ∈ R) (z : coordSub W (R : Set (Fin n)))
    (hz : ∀ t, t ≠ l → (z : PiLp 2 (fun i => (W i : Submodule ℝ H))) t = 0) :
    ‖(Ring.inverse (blk (bochnerOp W) (coordSub W (R : Set (Fin n))) (coordSub W (R : Set (Fin n)))) z :
        PiLp 2 (fun i => (W i : Submodule ℝ H))) k‖ ≤
      ((1 - S).submatrix ((↑) : R → Fin n) ((↑) : R → Fin n))⁻¹ ⟨k, hk⟩ ⟨l, hl⟩ *
        ‖(z : PiLp 2 (fun i => (W i : Submodule ℝ H))) l‖ := by sorry

end BlockBochner
