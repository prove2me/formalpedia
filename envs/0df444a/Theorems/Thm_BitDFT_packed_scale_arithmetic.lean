-- Prove2me | Theorems.Thm_BitDFT_packed_scale_arithmetic
-- name    : BitDFT.packed_scale_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T21:57:04.483352+00:00
-- url     : https://prove2.me/theorems/44bea75d-44e2-4a44-8597-3d176245330d
-- title:
--   Pack exact vector rescaling into bounded multiplier calls
-- statement:
--   Let a vector contain n nonnegative q-bit magnitudes and let n≤2^ℓ. Pack coefficients as little-endian base-2^(q+ℓ+1) digits. Multiplying the packed integer by n is exactly the packing of the individually scaled coefficients; every scaled coefficient fits its digit, and the packed result uses one digit per entry. If q≥ℓ, blocks of at most floor(n/4) entries fit in nq bits, and at most five such blocks cover any n≥12. Thus a fixed number of multiplier calls at the exact nq-bit bound can scale the large-vector case, without assuming the multiplier runtime bound is monotone.
-- source:
--   Arithmetic core for constructing BitDFT.rescale_output_machine. The block-width estimate supports calls to the arbitrary supplied multiplier only at sizes covered by T(nq); small n is handled with a constant number of q-bit calls covered by nT(q).

import Definitions.Def_BitDFT_PackedScale
set_option autoImplicit false
open BitDFT.PackedScale

theorem BitDFT.packed_scale_arithmetic :
    (∀ B n xs, packBase B (xs.map (fun a => n * a)) = n * packBase B xs) ∧
    (∀ B, 0 < B → ∀ xs, (∀ a ∈ xs, a < B) → packBase B xs < B ^ xs.length) ∧
    (∀ n q ell, n ≤ 2 ^ ell → ∀ xs, (∀ a ∈ xs, a < 2 ^ q) →
      (∀ a ∈ xs.map (fun a => n * a), a < 2 ^ (q + ell + 1)) ∧
      packBase (2 ^ (q + ell + 1)) (xs.map (fun a => n * a)) =
        n * packBase (2 ^ (q + ell + 1)) xs ∧
      packBase (2 ^ (q + ell + 1)) (xs.map (fun a => n * a)) <
        (2 ^ (q + ell + 1)) ^ xs.length) ∧
    (∀ n q ell r, 1 ≤ q → ell ≤ q → 4 * r ≤ n →
      r * (q + ell + 1) ≤ n * q) ∧
    (∀ n, 12 ≤ n → n ≤ 5 * (n / 4)) := by sorry
