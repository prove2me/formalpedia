-- Prove2me | Theorems.Thm_AESIndependence_Main_short_cnot
-- name    : AESIndependence.Main.short_cnot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:12:01.529693+00:00
-- url     : https://prove2.me/theorems/e13c67f6-6bd1-44b2-b586-cb60db9b4161
-- title:
--   Lemma 5.5 — short word for CNOT
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   For any two distinct bits $c,t$, even in the same byte, the binary gate
--   $$(x_c,x_t)\longmapsto(x_c,x_t+x_c)$$
--   has a gadget word of length at most $Kb$, using only depths $\{-2,-1,0,1\}$. One positive absolute $K$ works for all $b\ge4,d\ge2$, cipher parameters and bit locations. Every other state bit is fixed, including helpers whose initial values are arbitrary. The word and its keys do not depend on the input. This supplies the un-conjugated gate used in the subsequent depth shift.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - encoding: a sequence of gadgets whose product acts on every state → a finite list in application order, equality of its evaluation functions on the whole state space, with integer depths; reason: Equality includes every unmentioned byte and bit and restores helpers with arbitrary initial contents.
--   - encoding: O(b) with an absolute hidden constant → one positive real K before b,d,F,basis,A,C and every gate, key, index or scalar; word length at most K b; reason: The source gives no numeral; a uniform existential witness preserves the stated rate.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Lemma 5.5, p.19 (PDF p.19)

import Mathlib
import Definitions.Def_AESIndependence_Main_Gadgets

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem short_cnot :
    ∃ K : ℝ, 0 < K ∧ ∀ (b d : ℕ), 4 ≤ b → 2 ≤ d →
    ∀ (F : Type) [Field F] [Algebra (ZMod 2) F] [Fintype F]
      (D : Cipher b d F),
    ∀ (c t : BitIndex b d) (hct : c ≠ t),
      HasGadgetWord D gateDepths (K * b) (stateGate D (.cnot c t hct)) := by sorry

end AESIndependence.Main
