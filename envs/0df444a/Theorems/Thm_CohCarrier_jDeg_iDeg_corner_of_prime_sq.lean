-- Prove2me | Theorems.Thm_CohCarrier_jDeg_iDeg_corner_of_prime_sq
-- name    : CohCarrier.jDeg_iDeg_corner_of_prime_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/d8a5e996-0908-5199-be12-0fb76c58da0d
-- title:
--   Corner compositions of degeneracy maps at level Nq²
-- statement:
--   Let $N$ and $q$ be nonzero natural numbers, $A$ an additive abelian group, and suppose $q$ is prime and does not divide $N$. Suppose given two instances of the project's predicate `LevelLE` for the pair of levels $N \mid Nq^2$ with the full unit subgroups $\top$ at both levels, namely `h1` with divisor parameter $1$ and `hq2` with divisor parameter $q^2$; `LevelLE M M' H H' d` asserts $M \mid M'$, $d \mid M'/M$ and that reduction modulo $M$ carries $H'$ into $H$. Then for every $\varphi$ in `H1 N ⊤ A` both "corner" composites of the degeneracy maps between levels $N$ and $Nq^2$ coincide with $T_q \circ T_q - (q+1)\,\mathrm{id}$: first, the transfer map `jDeg` attached to the divisor-$1$ embedding applied to the pullback `iDeg'` along the divisor-$q^2$ embedding, and second, the transfer attached to the divisor-$q^2$ embedding applied to the pullback along the divisor-$1$ embedding, each equals `heckeT N ⊤ q A` applied twice to $\varphi$ minus $((q:\mathbb{Z})+1)\cdot\varphi$. Here `iDeg'` is precomposition with the embedding `iotaDeg` of $\Gamma_H$-groups given by conjugation by the relevant lower-triangular matrix, `jDeg` is the group-theoretic transfer of the character transported along the isomorphism onto the range of `iotaDeg`, and `heckeT` is the transfer from `GammaHUpper N ⊤ q` of $\varphi$ composed with `conjL`.
--
--   This is one of the composition relations between the degeneracy maps at levels $N$ and $Nq^2$, in the cohomological (transfer) formulation used here: the two extreme corner composites both realise the double coset of $\mathrm{diag}(1,q^2)$, and the resulting identity is the Hecke-ring relation $T(q)^2 = T(q^2) + (q+1)T(q,q)$ with $T(q,q)$ acting trivially, so the scalar is $q+1$ rather than the $q$ occurring in $T_q^2 = T_{q^2} + q\langle q\rangle$. It is collected, together with the remaining compositions, in [`CohCarrier.jDeg_iDeg_nine_identities_of_prime`](thm.html#CohCarrier.jDeg_iDeg_nine_identities_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_iDeg_corner_of_prime_sq.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CohCarrier in

theorem CohCarrier.jDeg_iDeg_corner_of_prime_sq (N q : ℕ) [NeZero N] [NeZero q]
    (A : Type) [AddCommGroup A] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2)) :
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) := by sorry
