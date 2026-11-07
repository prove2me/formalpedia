-- Prove2me | Theorems.Thm_DetANN_parseval_signed_blocks
-- name    : DetANN.parseval_signed_blocks
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:23.550616+00:00
-- url     : https://prove2.me/theorems/bcc46c65-416f-4cc2-ba6d-d573e7fd8f4b
-- title:
--   §6.1, p.14 — Parseval $\sum_j\|A_jz\|^2=\|z\|^2$ for every sign assignment
-- statement:
--   Let $h$ be a real $d\times d$ matrix with $h^\top h=d\,I$ (for instance the unnormalized Walsh–Hadamard matrix), $H=d^{-1/2}h$, $L\ge1$, and let $\xi^{(1)},\dots,\xi^{(L)}\in\{-1,+1\}^d$ be arbitrary. The signed blocks $(A_jz)_\ell=(Ld)^{-1/2}\sum_rh_{jr}\xi^{(\ell)}_rz_r$ satisfy, for every $z\in\mathbb R^d$,
--
--   $$\sum_{j=1}^d\|A_jz\|_2^2=\frac1L\sum_{\ell=1}^L\big\|H\,\mathrm{diag}(\xi^{(\ell)})z\big\|_2^2=\|z\|_2^2 .$$
--
--   So property (8) of a balanced block system holds whatever signs are chosen, and only (9) remains to be arranged.
--
--   Differences from the source:
--   - generalization: h the Walsh–Hadamard matrix (entries ±1, d a power of two) → any real d × d matrix h with hᵀh = d·I, any d; reason: the Walsh–Hadamard matrix satisfies hᵀh = d·I
--   - encoding: sign vectors in {−1, +1}^d → booleans mapped to ±1; reason: same assignments
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §6.1, p.14 (PDF p.14)

import Mathlib
import Definitions.Def_DetANN_SignedBlocks

namespace DetANN

/-- **Parseval for every sign choice** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §6.1, p.14).
For every assignment of the signs, the signed Hadamard blocks satisfy
`∑_j ‖A_j z‖² = (1/L) ∑_ℓ ‖H diag(ξ^(ℓ)) z‖² = ‖z‖²` for every `z ∈ ℝ^d`, where `H = d^{−1/2} h`.

**Formalization Note.** `h` is any real `d × d` matrix with `hᵀh = d·I` (the paper: the unnormalized
Walsh–Hadamard matrix, `d` a power of two, entries `±1`; it satisfies `hᵀh = d·I`). `L ≥ 1` (for
`L = 0` the blocks map into `ℝ^0`). The middle term is written out coordinatewise, with
`(H diag(ξ^(ℓ)) z)_j = d^{−1/2} ∑_r h_{jr} ξ^(ℓ)_r z_r`. -/
theorem parseval_signed_blocks {d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ)
    (hh : h.transpose * h = (d : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) (L : ℕ) (hL : 1 ≤ L)
    (ξ : Fin L → Fin d → Bool) (z : EuclideanSpace ℝ (Fin d)) :
    ∑ j, ‖signedBlocks h L ξ j z‖ ^ 2 =
        (1 / (L : ℝ)) * ∑ ℓ : Fin L, ∑ j : Fin d,
          ((Real.sqrt d)⁻¹ * ∑ r : Fin d, h j r * signOf (ξ ℓ r) * z r) ^ 2 ∧
      ∑ j, ‖signedBlocks h L ξ j z‖ ^ 2 = ‖z‖ ^ 2 := by sorry

end DetANN
