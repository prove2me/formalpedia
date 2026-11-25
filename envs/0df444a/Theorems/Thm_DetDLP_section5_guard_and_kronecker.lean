-- Prove2me | Theorems.Thm_DetDLP_section5_guard_and_kronecker
-- name    : DetDLP.section5_guard_and_kronecker
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:23:21.348028+00:00
-- url     : https://prove2.me/theorems/4955c26f-065a-4c26-9bbc-346088693fb9
-- title:
--   2-Adic Guard-Bit Exact Recovery, Kronecker Packing, and Nonnegative $L_1$-Norm Submultiplicativity
-- statement:
--   Establishes the three exact algebraic lemmas used in Proof of Theorem 4.3:
--
--   1. **2-adic guard-bit recovery:** if $0 \le r < 2^{P_0}$ and $0 \le \mathrm{acc} < 2^{P_0 + Q_{\mathrm{guard}}}$ with $\mathrm{acc} \equiv 2^{Q_{\mathrm{guard}}} r \pmod{2^{P_0 + Q_{\mathrm{guard}}}}$, then $\mathrm{acc} = 2^{Q_{\mathrm{guard}}} r$ and $\mathrm{acc} / 2^{Q_{\mathrm{guard}}} = r$;
--   2. **Kronecker packing:** $(i_1, i_2) \mapsto i_1 + K_0 i_2$ is injective on $i_1 < K_0$, maps $[0, K_0) \times [0, \ell)$ into $[0, K_0 \ell)$, and sends $i_2 \ge \ell$ to $\ge K_0 \ell$;
--   3. **Nonnegative polynomial $L_1$-norm submultiplicativity:** if $p_j(1) \le B$ over $\mathbb{N}[X]$, then $(\prod_j p_j)(1) \le B^n$ and every coefficient of $\prod_j p_j$ is at most $B^n$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 5.3, Proof of Theorem 4.3 (p. 22)

import Mathlib

set_option autoImplicit false

namespace DetDLP

/-- Algebraic core of Theorem 4.3 (Exact Digit Reduction, Kronecker Packing, and 2-Adic Guard-Bit
Recovery, Section 5.3, Proof of Theorem 4.3, p. 22):
1. Guard-bit exact recovery: if `0 ≤ r < 2^{P_0}` and `0 ≤ acc < 2^{P_0 + Q_guard}` satisfies
   `acc ≡ 2^{Q_guard} r (mod 2^{P_0 + Q_guard})`, then `acc = 2^{Q_guard} r` and `acc / 2^{Q_guard} = r`.
2. Kronecker packing `(i_1, i_2) ↦ i_1 + K_0 i_2`: injective for `i_1 < K_0`, maps `[0, K_0) × [0, ℓ)`
   into `[0, K_0 ℓ)`, and maps `i_2 ≥ ℓ` to `≥ K_0 ℓ` (clean truncation mod `W^{ℓ'}`).
3. Nonnegative polynomial `L_1`-norm submultiplicativity: if `∑_d coeff_d(p_j) ≤ B` for every
   `j ∈ Fin n`, then `(∏_j p_j)(1) ≤ B^n` and every coefficient of `∏_j p_j` is at most `B^n`. -/
theorem section5_guard_and_kronecker :
    (∀ P0 Qguard r acc : ℕ,
      r < 2 ^ P0 →
      acc < 2 ^ (P0 + Qguard) →
      (acc : ℤ) ≡ ((2 ^ Qguard * r : ℕ) : ℤ) [ZMOD ((2 ^ (P0 + Qguard) : ℕ) : ℤ)] →
      acc = 2 ^ Qguard * r ∧ acc / 2 ^ Qguard = r) ∧
    (∀ K0 ℓ : ℕ, 1 ≤ K0 → 1 ≤ ℓ →
      (∀ i1 i1' i2 i2' : ℕ, i1 < K0 → i1' < K0 →
        i1 + K0 * i2 = i1' + K0 * i2' → i1 = i1' ∧ i2 = i2') ∧
      (∀ i1 i2 : ℕ, i1 < K0 → i2 < ℓ → i1 + K0 * i2 < K0 * ℓ) ∧
      (∀ i1 i2 : ℕ, ℓ ≤ i2 → K0 * ℓ ≤ i1 + K0 * i2)) ∧
    (∀ (n B : ℕ) (p : Fin n → Polynomial ℕ),
      (∀ j : Fin n, (p j).eval 1 ≤ B) →
      (∏ j : Fin n, p j).eval 1 ≤ B ^ n ∧
      ∀ d : ℕ, (∏ j : Fin n, p j).coeff d ≤ B ^ n) := by
  sorry

end DetDLP
