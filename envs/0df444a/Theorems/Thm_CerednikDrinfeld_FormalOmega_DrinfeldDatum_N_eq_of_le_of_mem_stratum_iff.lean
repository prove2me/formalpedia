-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N_eq_of_le_of_mem_stratum_iff
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.N_eq_of_le_of_mem_stratum_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/8abe3ca1-f1c4-515b-955b-39f3704406b5
-- title:
--   Lattice squeeze along a base change of Drinfeld data
-- statement:
--   Let $p$ be a prime, and let $B$, $B'$ be commutative $\mathbb{Z}_p$-algebras with a $\mathbb{Z}_p$-algebra homomorphism $f : B \to B'$. Let $Q$ be a Drinfeld datum over $B$ and $Q'$ one over $B'$, both taken with $K = \mathbb{Q}_p$ and uniformiser $\pi = p \in \mathbb{Z}_p$; in particular each assigns to every prime of its base ring a pair of $\mathbb{Z}_p$-submodules $N_0 \le N_1$ of $\mathbb{Q}_p^2$ that are full lattices (finitely generated and spanning $\mathbb{Q}_p^2$ over $\mathbb{Q}_p$) with $p\,N_1 \subseteq N_0$, together with the remaining data of the structure (openness of the loci where a fixed vector lies in $N_0$ resp. $N_1$, invertible modules $T_0, T_1$ linked by maps composing to multiplication by $p$, comparison maps $u_0, u_1$ to the stalks, and the distinguished subsets $\mathrm{stratum}_0$, $\mathrm{stratum}_1$ of the prime spectrum with their determinant-index properties). Let $x'$ be a prime of $B'$ and write $x = f^{-1}(x')$ for the prime of $B$ obtained by pulling back along $f$. Assume $Q.N_0(x) \le Q'.N_0(x')$ and $Q.N_1(x) \le Q'.N_1(x')$, that $x' \in Q'.\mathrm{stratum}_i$ holds if and only if $x \in Q.\mathrm{stratum}_i$ for $i = 0, 1$, and that $x'$ lies in $Q'.\mathrm{stratum}_0$ or in $Q'.\mathrm{stratum}_1$. Then the inclusions are equalities: $Q'.N_0(x') = Q.N_0(x)$ and $Q'.N_1(x') = Q.N_1(x)$.
--
--   This is the rigidity step in the comparison of two Drinfeld data along a base change $B \to B'$ in the Čerednik–Drinfeld uniformisation: once the lattice functions of the source datum are known to be contained in those of the target at corresponding points and the stratifications match, they must agree. It is used in the verification that a rigidified special formal datum is obtained by base change, [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isBaseChangeAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N_eq_of_le_of_mem_stratum_iff.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.N_eq_of_le_of_mem_stratum_iff
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B] {B' : Type} [CommRing B'] [Algebra ℤ_[p] B']
    (f : B →ₐ[ℤ_[p]] B')
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (x' : PrimeSpectrum B')
    (h₀ : Q.N₀ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₀ x')
    (h₁ : Q.N₁ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₁ x')
    (hs₀ : x' ∈ Q'.stratum₀ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₀)
    (hs₁ : x' ∈ Q'.stratum₁ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₁)
    (hcov : x' ∈ Q'.stratum₀ ∨ x' ∈ Q'.stratum₁) :
    Q'.N₀ x' = Q.N₀ (DrinfeldDatum.pointUnder f x') ∧ Q'.N₁ x' = Q.N₁ (DrinfeldDatum.pointUnder f x') := by sorry
