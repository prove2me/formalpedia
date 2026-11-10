-- Prove2me | Theorems.Thm_AESIndependence_Main_balanced_gates
-- name    : AESIndependence.Main.balanced_gates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:11:57.388271+00:00
-- url     : https://prove2.me/theorems/17da27d7-5df9-4304-925c-fc41f9cc2f07
-- title:
--   Theorem 3.2 — balanced gate simulation
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   There is a positive absolute $K$ such that, for every admissible cipher with $b\ge4,d\ge2$ and every NOT, CNOT or Toffoli gate $G$, there is a fixed integer length $\ell_G\le Kb$ and a law on $\ell_G$ seven-key labels satisfying
--   $$w_{\ell_G}\cdots w_1=M^{-2}GM^2.$$
--   This equality holds for every sequence of positive mass and for every input. Each label position is exactly uniform on the full seven-key product space, while positions may be correlated. The law is independent of the starting state, so it works simultaneously for all starting tuples. These are all three clauses of the source theorem: fixed length, exact simulation, and balanced marginals.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - encoding: W-edges with uniform marginals → PMFs on fixed-length sequences of seven-key labels, with each marginal equal to the product-uniform key law; reason: Labels are retained even when they induce identical permutations; no independence between sequence positions or dependence on a starting state is introduced.
--   - encoding: O(b) with an absolute hidden constant → one positive real K before b,d,F,basis,A,C and every gate, key, index or scalar; word length at most K b; reason: The source gives no numeral; a uniform existential witness preserves the stated rate.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Theorem 3.2, p.15 (PDF p.15)

import Mathlib
import Definitions.Def_AESIndependence_Main_Gadgets

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem balanced_gates :
    ∃ K : ℝ, 0 < K ∧ ∀ (b d : ℕ), 4 ≤ b → 2 ≤ d →
    ∀ (F : Type) [Field F] [Algebra (ZMod 2) F] [Fintype F]
      (D : Cipher b d F),
    ∀ G : Gate (BitIndex b d), ∃ ℓ : ℕ, (ℓ : ℝ) ≤ K * b ∧
      BalancedSimulation (fun v => (wPermutation D v : State d F → State d F))
        (PMF.uniformOfFintype (WLabel d F)) ℓ (conjugatedGate D G) := by sorry

end AESIndependence.Main
