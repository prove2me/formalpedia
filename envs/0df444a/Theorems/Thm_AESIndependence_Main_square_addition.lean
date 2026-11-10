-- Prove2me | Theorems.Thm_AESIndependence_Main_square_addition
-- name    : AESIndependence.Main.square_addition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:11:37.189687+00:00
-- url     : https://prove2.me/theorems/d82307a0-8825-40fc-bf86-119368a76181
-- title:
--   Corollary 5.15 — square addition
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   For any distinct byte locations $i,k$, the map
--   $$x_k\longmapsto x_k+x_i^2$$
--   fixes every other byte and has a word of length at most $K$. One positive absolute constant $K$ works simultaneously for every admissible cipher with $b\ge4,d\ge2$, every location. The word is fixed independently of the input. In particular, helper bytes have arbitrary initial contents and must be restored. This is a synthesis interface for the source’s later reversible operations.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - encoding: a sequence of gadgets whose product acts on every state → a finite list in application order, equality of its evaluation functions on the whole state space, with integer depths; reason: Equality includes every unmentioned byte and bit and restores helpers with arbitrary initial contents.
--   - encoding: O(1) gadgets → one positive real K before b,d,F,basis,A,C and all byte locations and coefficients; length at most K; reason: The witness is absolute rather than depending on an instance.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Corollary 5.15, p.27 (PDF p.27)

import Mathlib
import Definitions.Def_AESIndependence_Main_Gadgets

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem square_addition :
    ∃ K : ℝ, 0 < K ∧ ∀ (b d : ℕ), 4 ≤ b → 2 ≤ d →
    ∀ (F : Type) [Field F] [Algebra (ZMod 2) F] [Fintype F]
      (D : Cipher b d F),
    ∀ (i k : ByteIndex d), i ≠ k →
      HasGadgetWord D Set.univ (K) (squareAddition i k) := by sorry

end AESIndependence.Main
