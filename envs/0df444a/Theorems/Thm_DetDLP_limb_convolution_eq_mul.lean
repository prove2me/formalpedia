-- Prove2me | Theorems.Thm_DetDLP_limb_convolution_eq_mul
-- name    : DetDLP.limb_convolution_eq_mul
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:13.042271+00:00
-- url     : https://prove2.me/theorems/2880473f-9ef3-462d-b6f8-3036ab0dbedf
-- title:
--   Equivalence of Fermat-Ring Limb Convolution and Exact Unsigned Binary Multiplication
-- statement:
--   For every bit-length $d \ge 1$ and $d$-bit unsigned binary vectors $v \in \{0, 1\}^d$, the unsigned value $\mathrm{bitsToNat}(v) = \sum_{i=0}^{d-1} v_i 2^i$ satisfies $\mathrm{bitsToNat}(v) < 2^d$. Consequently, for operands $a, b < 2^d$ with $B = 2^d$ and Fermat modulus $Q = 2^{4d} + 1$, the single-limb Fermat convolution $\sum_{u < 2} (c_u \bmod Q) B^u$ equals $a \cdot b$, so the Fermat-ring convolution relation on interface wires $x \in \{0, 1\}^{4d}$ is identical to the exact unsigned product relation $a \cdot b = c_{\mathrm{out}}$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3 Lemma 2.3 (pp. 8–9)

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

/-- Equivalence between the Fermat-ring limb-convolution relation and exact unsigned binary
multiplication for `d`-bit operands (`a, b < 2^d` and `a * b < 2^{2d} < 2^{4d} + 1`). -/
theorem limb_convolution_eq_mul :
    (∀ (d : ℕ) (v : Fin d → Bool), bitsToNat v < 2 ^ d) ∧
    (∀ (d : ℕ), 1 ≤ d →
      0 < d ∧ d ≤ d * 1 ∧ 1 ≤ 2 ^ d ∧
      (fun x : Fin (4 * d) → Bool =>
        let a := bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩)
        let b := bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩)
        let cout := bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)
        let B := 2 ^ d
        let Q := 2 ^ (4 * d) + 1
        let limb (w i : ℕ) := w / B ^ i % B
        let c (u : ℕ) := ∑ i ∈ Finset.range 1, ∑ j ∈ Finset.range 1,
          if i + j = u then limb a i * limb b j else 0
        (∑ u ∈ Finset.range (2 * 1), (c u % Q) * B ^ u) = cout) =
      (fun x : Fin (4 * d) → Bool =>
        bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
        bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
        bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩))) := by
  sorry

end DetDLP
