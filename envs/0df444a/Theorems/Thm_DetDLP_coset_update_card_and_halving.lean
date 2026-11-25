-- Prove2me | Theorems.Thm_DetDLP_coset_update_card_and_halving
-- name    : DetDLP.coset_update_card_and_halving
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:23:33.577654+00:00
-- url     : https://prove2.me/theorems/56b39b11-4c3b-41e4-adec-03e3cc973bf4
-- title:
--   Exact Coset Index Formula and Halving-on-Violation Modulo $M_{\mathrm{lab}}$
-- statement:
--   For any $M_{\mathrm{lab}} \ge 2$, $N \ge 1$, modular affine solution coset $\mathcal{A} = (x_0 + B\mathbb{Z}^N)/M_{\mathrm{lab}}\mathbb{Z}^N$, and linear congruence $a^\top x \equiv c_0 \pmod{M_{\mathrm{lab}}}$ whose intersection $\mathcal{A}'$ with $\mathcal{A}$ is nonempty, let $g_* = \gcd(a^\top b_1, \dots, a^\top b_N, M_{\mathrm{lab}})$. Then:
--
--   1. $|\mathcal{A}'| \cdot M_{\mathrm{lab}} = |\mathcal{A}| \cdot g_*$;
--   2. Whenever $a^\top x_0 \not\equiv c_0 \pmod{M_{\mathrm{lab}}}$, we have $g_* < M_{\mathrm{lab}}$ and $2 |\mathcal{A}'| \le |\mathcal{A}|$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.3, Proof of Lemma 4.4 (p. 17)

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

namespace DetDLP

/-- Pure algebraic core of Lemma 4.4 (Section 4.3, p. 17):
for any `Mlab ≥ 2`, `N ≥ 1`, modular affine coset `A = affineCoset Mlab x0 B`, and linear
congruence `∑ i, a i * x i = c0` whose intersection `A'` with `A` is nonempty, letting
`gstar = gcd(aᵀ b₁, ..., aᵀ b_N, Mlab)`:
(a) `Nat.card A' * Mlab = Nat.card A * gstar`;
(b) if `∑ i, a i * x0 i ≠ c0`, then `gstar < Mlab` and `2 * Nat.card A' ≤ Nat.card A`. -/
theorem coset_update_card_and_halving :
    ∀ (Mlab N : ℕ) [NeZero Mlab], 2 ≤ Mlab → 1 ≤ N →
      ∀ (x0 : Fin N → ZMod Mlab) (B : Matrix (Fin N) (Fin N) ℤ)
        (a : Fin N → ZMod Mlab) (c0 : ZMod Mlab),
        let A := affineCoset Mlab x0 B
        let A' := {x ∈ A | ∑ i : Fin N, a i * x i = c0}
        A'.Nonempty →
        let gstar : ℕ :=
          Finset.univ.fold Nat.gcd Mlab
            (fun j : Fin N => Int.natAbs (∑ i : Fin N, ((a i).val : ℤ) * B i j))
        Nat.card A' * Mlab = Nat.card A * gstar ∧
        ((∑ i : Fin N, a i * x0 i ≠ c0) → gstar < Mlab ∧ 2 * Nat.card A' ≤ Nat.card A) := by
  sorry

end DetDLP
