-- Prove2me | Theorems.Thm_AESIndependence_Main_main_theorem
-- name    : AESIndependence.Main.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:10:48.735081+00:00
-- url     : https://prove2.me/theorems/025fa80a-2f4a-4a5d-8e5d-c41ce61644f3
-- title:
--   Theorem 3.1 — polynomial-round approximate t-wise independence of generalized AES
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   There is one absolute real $B>0$ such that, for every $b\ge4,d\ge2$, every allowed field, basis and matrices, all $2\le t\le2^n-2$, every $0<\varepsilon<1$ and every integer
--   $$r\ge\left\lceil Bn^2b^2\bigl(nt+\ln(1/\varepsilon)\bigr)\right\rceil,$$
--   the joint ciphertext distribution at every ordered tuple of $t$ distinct plaintexts has total variation distance at most $\varepsilon$ from the uniform law on ordered injective tuples.
--   The encryption is $F^0(x)=x+K_0$ and $F^{i+1}(x)=M(F^i(x))+K_{i+1}$; the entire sequence $K_0,\ldots,K_r$ is independent and uniform and is shared across all evaluations. The witness $B$ precedes every parameter, including the basis, both linear maps, tuple size, error and plaintexts. The theorem assumes no gap, balanced simulation, expander witness or independence conclusion. This is the full source result for the independent-key generalized cipher; it makes no ten-round AES-128 or master-key schedule claim.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - encoding: O(n²b²(nt+log(1/ε))) rounds with an absolute hidden constant → ∃ B>0 before every parameter, and every r at least the natural ceiling of B n²b²(nt+ln(1/ε)); reason: Natural rounding and the logarithm base are absorbed only into the one universal constant; the polynomial and full tuple range are unchanged.
--   - encoding: statistical distance from a uniform permutation on t fixed distinct plaintexts → finite total variation between the product-key ciphertext pushforward and uniform mass on the injective-tuple subtype; reason: Uniform permutation evaluation is exactly uniform on ordered distinct tuples; independent possibly-colliding samples are not used.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Theorem 3.1, p.14 (PDF p.14)

import Mathlib
import Definitions.Def_AESIndependence_Main_CipherModel

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem main_theorem :
    ∃ B : ℝ, 0 < B ∧ ∀ (b d : ℕ), 4 ≤ b → 2 ≤ d →
    ∀ (F : Type) [Field F] [Algebra (ZMod 2) F] [Fintype F]
      (D : Cipher b d F),
    ∀ t : ℕ, 2 ≤ t → t ≤ 2^(bitCount b d) - 2 →
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ r : ℕ,
      ⌈B * (bitCount b d : ℝ)^2 * (b : ℝ)^2 *
        ((bitCount b d : ℝ) * t + Real.log (1 / ε))⌉₊ ≤ r →
      ∀ x : DistinctTuple (State d F) t, cipherTV D r x ≤ ε := by sorry

end AESIndependence.Main
