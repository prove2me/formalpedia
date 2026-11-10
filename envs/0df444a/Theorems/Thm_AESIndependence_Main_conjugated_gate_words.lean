-- Prove2me | Theorems.Thm_AESIndependence_Main_conjugated_gate_words
-- name    : AESIndependence.Main.conjugated_gate_words
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:11:59.950824+00:00
-- url     : https://prove2.me/theorems/b23b60a3-f09b-4c6e-9f4d-1a65ba9924f7
-- title:
--   Lemma 5.1 — short words for conjugated gates
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   For any NOT, CNOT or Toffoli gate $G$ on the $n$ actual state bits, there is a fixed word such that
--   $$h_{v_s}^{(j_s)}\cdots h_{v_1}^{(j_1)}=M^{-2}GM^2,\qquad s\le Kb,\qquad j_i\in\{0,1,2,3\}.$$
--   One positive absolute constant $K$ works uniformly over every admissible $b\ge4,d\ge2$, basis, cipher and gate. Keys and depths are independent of the input. Equality on every state fixes all bit behavior and permits no ancillary wires. This is the exact symbolic interface that the balanced gadget lemma can simulate.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - encoding: a sequence of gadgets whose product acts on every state → a finite list in application order, equality of its evaluation functions on the whole state space, with integer depths; reason: Equality includes every unmentioned byte and bit and restores helpers with arbitrary initial contents.
--   - encoding: O(b) with an absolute hidden constant → one positive real K before b,d,F,basis,A,C and every gate, key, index or scalar; word length at most K b; reason: The source gives no numeral; a uniform existential witness preserves the stated rate.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Lemma 5.1, p.18 (PDF p.18)

import Mathlib
import Definitions.Def_AESIndependence_Main_Gadgets

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem conjugated_gate_words :
    ∃ K : ℝ, 0 < K ∧ ∀ (b d : ℕ), 4 ≤ b → 2 ≤ d →
    ∀ (F : Type) [Field F] [Algebra (ZMod 2) F] [Fintype F]
      (D : Cipher b d F),
    ∀ G : Gate (BitIndex b d),
      HasGadgetWord D balancedDepths (K * b) (conjugatedGate D G) := by sorry

end AESIndependence.Main
