-- Prove2me | Theorems.Thm_AESIndependence_Main_gap_to_cipher_mixing
-- name    : AESIndependence.Main.gap_to_cipher_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:10:56.983819+00:00
-- url     : https://prove2.me/theorems/1c0ee3a0-3303-44c1-9b16-1cff4a5f1d22
-- title:
--   Corollary 2.17 — from the symmetrized gap to actual AES mixing
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   Let $\Omega_t$ have at least two states, form $P$ by independent uniform pre- and post-round keys, and set $W=(P^3)^\mathsf TP^3$. If $\lambda_2(W)<1$, then one absolute $C>0$ works for every cipher, tuple size and $0<\varepsilon<1$: every integer round count
--   $$r\ge\left\lceil\frac{6C}{\operatorname{gap}(W)}\bigl(nt+\ln(1/\varepsilon)\bigr)\right\rceil$$
--   has ciphertext law at total variation distance at most $\varepsilon$ from uniform on $\Omega_t$, for every distinct plaintext tuple. The ciphertext law is that of the concrete independently keyed recursion, not powers of $W$. The factor six explicitly retains the nonreversible transfer stated in Theorem 2.16. This conditional result supplies the last interface of the headline proof; its gap premise is absent from Theorem 3.1.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - encoding: O(gap(W)⁻¹(nt+log(1/ε))) rounds; Theorem 2.16 gives a factor 6 → one absolute C>0 before all parameters, a natural ceiling with factor 6C, and all integer r above it; reason: Natural rounding and logarithm base change only the universal constant; no numerical value of C is asserted.
--   - encoding: λ₂(W) is defined and strictly below 1 → at least two tuple states, lambdaTwo=1−gap for W=(P³)ᵀP³; reason: This excludes only cases where a second eigenvalue is undefined; a positive gap ensures the division is legitimate.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Corollary 2.17 and Theorem 2.16, p.13 (PDF p.13)

import Mathlib
import Definitions.Def_AESIndependence_Main_CipherModel

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem gap_to_cipher_mixing :
    ∃ C : ℝ, 0 < C ∧
    ∀ (b d : ℕ) (F : Type) [Field F] [Algebra (ZMod 2) F] [Fintype F]
      (D : Cipher b d F) (t : ℕ),
      2 ≤ Fintype.card (DistinctTuple (State d F) t) →
      lambdaTwo (wMatrix D t) < 1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ r : ℕ,
        ⌈(6 * C) / spectralGap (wMatrix D t) *
          ((bitCount b d : ℝ) * t + Real.log (1 / ε))⌉₊ ≤ r →
        ∀ x : DistinctTuple (State d F) t, cipherTV D r x ≤ ε := by sorry

end AESIndependence.Main
