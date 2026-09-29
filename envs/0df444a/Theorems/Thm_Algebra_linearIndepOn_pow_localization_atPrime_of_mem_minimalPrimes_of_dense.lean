-- Prove2me | Theorems.Thm_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense
-- name    : Algebra.linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/40625262-2986-51b3-96d7-f4d6a50185c6
-- title:
--   Mac Lane separability descends to minimal primes
-- statement:
--   Let $k$ be a field and $B$ a reduced commutative $k$-algebra of finite type, both in the same universe, and let $p$ be a prime number which is an exponential characteristic of $k$ (so $p$ is the characteristic of $k$, the case $p=1$ being excluded by primality). Let $S$ be a set of points of the prime spectrum of $B$ subject to two hypotheses: a density hypothesis, that any $g \in B$ lying in the prime ideal $\mathfrak{s}.\mathrm{asIdeal}$ for every $\mathfrak{s} \in S$ vanishes; and a separability hypothesis, that for each $\mathfrak{s} \in S$ there is a field $K$, again in the same universe, with a $k$-algebra structure, such that for every finite subset $t$ of $K$ which is $k$-linearly independent (as a family indexed by itself via the identity) the family of $p$-th powers of the elements of $t$ is also $k$-linearly independent, and such that the residue field of $\mathfrak{s}.\mathrm{asIdeal}$ admits a $k$-algebra homomorphism into $K$. Let $\mathfrak{q}$ be a prime ideal of $B$ that is a minimal prime of $B$, and let $s$ be a finite subset of the localisation $B_{\mathfrak{q}}$ which is $k$-linearly independent. The conclusion is that the family of $p$-th powers of the elements of $s$ is $k$-linearly independent over $k$ in $B_{\mathfrak{q}}$.
--
--   This is the transfer step in the classical result that a reduced scheme of finite type over a field with a dense set of separably generated points is generically smooth: Mac Lane's criterion for separability, in the form 'linearly independent families have linearly independent $p$-th powers', passes from a dense family of residue fields to the residue fields at the minimal primes. It is used by [`Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField`](thm.html#Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField), where the $p$-th-power hypothesis is obtained from formal smoothness of the target field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      (∀ t : Finset K, LinearIndepOn k _root_.id (t : Set K) → LinearIndepOn k (· ^ p) (t : Set K)) ∧
      Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B)
    (s : Finset (Localization.AtPrime 𝔮)) (hs : LinearIndepOn k _root_.id (s : Set (Localization.AtPrime 𝔮))) :
    LinearIndepOn k (· ^ p) (s : Set (Localization.AtPrime 𝔮)) := by sorry
