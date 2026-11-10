-- Prove2me | Theorems.Thm_AESIndependence_Main_short_not
-- name    : AESIndependence.Main.short_not
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:11:54.973161+00:00
-- url     : https://prove2.me/theorems/e3512765-e304-47c4-b493-966c2b92896b
-- title:
--   Lemma 5.4 — a one-gadget NOT word
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   For every binary position $p$, let $e_p$ be the full-state mask with just that basis bit set. Then
--   $$\operatorname{NOT}_p=T_{e_p}=h_{e_p}^{(0)}.$$
--   There is a word of exactly one gadget, at depth zero, implementing this gate on every state. The mask is a bit mask rather than the byte-unit vector used elsewhere. This fixes the base gate interface without any asymptotic constant.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - encoding: a sequence of gadgets whose product acts on every state → a finite list in application order, equality of its evaluation functions on the whole state space, with integer depths; reason: Equality includes every unmentioned byte and bit and restores helpers with arbitrary initial contents.
--   - reading: e_i in the NOT identity → the mask with exactly the selected basis bit set; reason: The source uses e for both byte and bit indicators; §2.1 and the NOT operation fix this interpretation.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Lemma 5.4, p.19 (PDF p.19)

import Mathlib
import Definitions.Def_AESIndependence_Main_Gadgets

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem short_not {b d : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (D : Cipher b d F) (p : BitIndex b d) :
    stateGate D (.not p) = (translation (bitMask D p) : State d F → State d F) ∧
    translation (bitMask D p) = gadget D 0 (bitMask D p) ∧
    ∃ w : GadgetWord d F, w.length = 1 ∧ (∀ a ∈ w, a.1 = 0) ∧
      gadgetWordAction D w = stateGate D (.not p) := by sorry

end AESIndependence.Main
