-- Prove2me | Theorems.Thm_AESIndependence_Main_affine_bytes
-- name    : AESIndependence.Main.affine_bytes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:11:47.080748+00:00
-- url     : https://prove2.me/theorems/7b162086-ad0e-43b6-880d-d4bda0048f7f
-- title:
--   Proposition 5.11 — affine operations on all bytes
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   Assume $b\ge4$. For arbitrary nonzero scalars $\alpha_q\in F$ and offsets $c_q\in F$ at every byte location $q$, the simultaneous map
--   $$x_q\longmapsto \alpha_qx_q+c_q\quad\text{for every }q$$
--   has a gadget word of length at most eleven, all of whose depths are zero or one. The bound is independent of $d$, and the word works on every input. This supplies simultaneous affine byte synthesis with the exact printed constant.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - encoding: a sequence of gadgets whose product acts on every state → a finite list in application order, equality of its evaluation functions on the whole state space, with integer depths; reason: Equality includes every unmentioned byte and bit and restores helpers with arbitrary initial contents.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Proposition 5.11, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_AESIndependence_Main_Gadgets

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem affine_bytes {b d : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (hb : 4 ≤ b) (D : Cipher b d F) (α c : ByteIndex d → F)
    (hα : ∀ i, α i ≠ 0) :
    HasGadgetWord D {0, 1} 11 (affineBytes α c) := by sorry

end AESIndependence.Main
