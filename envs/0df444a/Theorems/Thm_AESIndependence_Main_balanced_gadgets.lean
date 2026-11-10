-- Prove2me | Theorems.Thm_AESIndependence_Main_balanced_gadgets
-- name    : AESIndependence.Main.balanced_gadgets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:11:49.794018+00:00
-- url     : https://prove2.me/theorems/8e989e09-c699-41c4-8f65-ce0aa4a51f69
-- title:
--   Lemma 4.2 — balanced simulation of gadgets
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   For every $j\in\{0,1,2,3\}$ and every full-state key $v$, there is one law on sequences of seven-key labels of exactly $2+4j$ positions such that
--   $$w_{2+4j}\cdots w_1=h_v^{(j)}$$
--   for every sequence of positive mass, as an equality on all inputs. Every label position has the uniform product law on seven independent keys. Positions within a sequence may be correlated. Therefore the same law supplies the required path for every starting tuple. This is the balanced interface used for gadget substitution.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - encoding: W-edges with uniform marginals → PMFs on fixed-length sequences of seven-key labels, with each marginal equal to the product-uniform key law; reason: Labels are retained even when they induce identical permutations; no independence between sequence positions or dependence on a starting state is introduced.
--   - reading: the printed key type is F_(2^b)^k, with k not defined in that sentence → v ranges over the entire d by d state; reason: Definition 4.1 calls v a round key, whose full-state type is fixed by Definition 2.7.
--   - encoding: j in {0,1,2,3} → j is natural with j ≤ 3; reason: Natural depth is coerced to the integer exponent of the gadget; this retains exactly the four depths.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Lemma 4.2, p.16 (PDF p.16)

import Mathlib
import Definitions.Def_AESIndependence_Main_Gadgets

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem balanced_gadgets {b d : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F] [Fintype F]
    (D : Cipher b d F) (j : ℕ) (hj : j ≤ 3) (v : State d F) :
    BalancedSimulation (fun w => (wPermutation D w : State d F → State d F))
      (PMF.uniformOfFintype (WLabel d F)) (2 + 4*j) (gadget D (j : ℤ) v) := by sorry

end AESIndependence.Main
