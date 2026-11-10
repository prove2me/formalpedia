-- Prove2me | Theorems.Thm_AESIndependence_Main_reference_gap
-- name    : AESIndependence.Main.reference_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:13:07.744683+00:00
-- url     : https://prove2.me/theorems/40330322-f806-4069-b7c3-e37ec12aa999
-- title:
--   Proposition 2.21 — spectral gap of the reference tuple chain
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   Let $c\ge1$ and let $g_1,\ldots,g_c$ be even permutations of the binary assignment space whose lazy alternating-group Cayley walk has gap at least $\gamma>0$. Use the fixed basis to identify binary assignments and states. For every $2\le t\le2^n-2$, the corresponding conjugated tuple chain satisfies
--   $$\operatorname{gap}(K_{\rm ref})\ge\gamma,\qquad K_{\rm ref}=\frac12I+\frac1{4c}\sum_i(M^{-2}g_iM^2+M^{-2}g_i^{-1}M^2).$$
--   This includes the generators and the same lower bound supplied by Theorem 2.19. Circuit complexity and distinctness of generators are not needed for this transfer. The tuple chain is not identified with the group Cayley chain.
--
--   Differences from the source:
--   - encoding: field-valued d by d states with fixed binary coordinates and invertible matrices A and C → ByteIndex d = Fin d × Fin d, a fixed binary basis, and linear equivalences A over F₂ and C over F with nonzero matrix entries for C and its inverse; reason: These represent exactly the source matrices and every state; C is not required to be MDS and A is not required to be F-linear.
--   - generalization: the specific generator family and lower bound from Theorem 2.19 → any positive-gap even-generator family with c ≥ 1, without a circuit-size or distinctness premise; reason: The transitive quotient and fixed conjugation transfer the gap for every such family; the source witness specializes directly.
--   - encoding: second eigenvalue with multiplicity → mean-zero Rayleigh gap and the actual weighted reference matrix on injective tuples; reason: This preserves all stationary modes; the stated t range makes the tuple space nontrivial.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Proposition 2.21 and Definition 2.20, p.14 (PDF p.14)

import Mathlib
import Definitions.Def_AESIndependence_Main_ReferenceChain

namespace AESIndependence.Main
open scoped BigOperators Classical

theorem reference_gap {b d : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F] [Fintype F]
    (hb : 4 ≤ b) (hd : 2 ≤ d) (D : Cipher b d F)
    {c : ℕ} (hc : 1 ≤ c) (g : Fin c → EvenPerm (BitIndex b d))
    (γ : ℝ) (hγ : 0 < γ) (hg : γ ≤ spectralGap (cayleyMatrix g))
    (t : ℕ) (ht : 2 ≤ t) (htop : t ≤ 2^(bitCount b d) - 2) :
    γ ≤ spectralGap (referenceMatrix D g t) := by sorry

end AESIndependence.Main
