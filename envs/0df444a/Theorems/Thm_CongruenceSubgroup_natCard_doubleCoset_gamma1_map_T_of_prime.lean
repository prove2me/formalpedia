-- Prove2me | Theorems.Thm_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_of_prime
-- name    : CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/d3acf0cb-1b04-55ce-b30d-ee3a9fd6336e
-- title:
--   Double cosets of the reduced Γ₁(p) and ⟨ T⟩ number 2(p-1)
-- statement:
--   Let $p$ be a natural number carrying an instance witnessing that it is prime. Consider the reduction homomorphism $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/p)$ obtained by applying the ring homomorphism $\mathbb{Z} \to \mathbb{Z}/p$ entrywise to $2 \times 2$ matrices (`Matrix.SpecialLinearGroup.map` of `Int.castRingHom (ZMod p)`). Form two subgroups of $\mathrm{SL}_2(\mathbb{Z}/p)$: the image under this map of the congruence subgroup $\Gamma_1(p) \le \mathrm{SL}_2(\mathbb{Z})$, and the image under the same map of the subgroup of integer powers of the modular matrix $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$. Regarding both subgroups as subsets of $\mathrm{SL}_2(\mathbb{Z}/p)$, the assertion is that the set of double cosets of $\mathrm{SL}_2(\mathbb{Z}/p)$ by these two subsets on the left and on the right is finite of cardinality $2(p-1)$, the number of double cosets being computed as a `Nat.card` and the right-hand side using truncated subtraction of naturals.
--
--   This is the local double-coset count underlying the classical formula for the number of cusps of $\Gamma_1(N)$, the two subgroups in question both reducing to the upper unipotent subgroup of $\mathrm{SL}_2(\mathbb{F}_p)$. It feeds the multiplicativity step [`CongruenceSubgroup.index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd`](thm.html#CongruenceSubgroup.index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd), which combines the prime-level count with the level coprime to $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_of_prime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_of_prime
    (p : ℕ) [Fact p.Prime] :
    Nat.card (DoubleCoset.Quotient (((CongruenceSubgroup.Gamma1 p).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod p)))) : Set SL(2, ZMod p)) (((Subgroup.zpowers ModularGroup.T).map (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod p)))) : Set SL(2, ZMod p))) = 2 * (p - 1) := by sorry
