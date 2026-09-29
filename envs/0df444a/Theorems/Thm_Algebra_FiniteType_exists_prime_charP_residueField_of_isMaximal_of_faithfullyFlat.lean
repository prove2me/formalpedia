-- Prove2me | Theorems.Thm_Algebra_FiniteType_exists_prime_charP_residueField_of_isMaximal_of_faithfullyFlat
-- name    : Algebra.FiniteType.exists_prime_charP_residueField_of_isMaximal_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/531072da-fc64-5261-8850-f5f72dfe6c56
-- title:
--   Positive residue characteristic of faithfully flat local algebras
-- statement:
--   Let $S$ be a commutative ring that is a finitely generated (finite type) $\mathbb{Z}$-algebra, let $\mathfrak{p}$ be a point of the prime spectrum of $S$ whose underlying ideal $\mathfrak{p}.\mathrm{asIdeal}$ is maximal, and let $R$ be a commutative local ring carrying both an $S$-algebra structure and an algebra structure over the localisation $S_{\mathfrak{p}}$ of $S$ at $\mathfrak{p}.\mathrm{asIdeal}$, these being compatible in the sense that $S \to S_{\mathfrak{p}} \to R$ is a scalar tower. Assume that $R$ is faithfully flat as a module over $S_{\mathfrak{p}}$. Then there exists a natural number $p$ which is prime and such that the residue field $R/\mathfrak{m}_R$ of the local ring $R$ has characteristic $p$, i.e. satisfies `CharP` for $p$.
--
--   This is the statement that a local ring faithfully flat over the local ring of a maximal point of an arithmetic scheme of finite type over $\mathbb{Z}$ has residue field of positive (prime) characteristic; the maximal ideal has finite residue field by the Nullstellensatz over $\mathbb{Z}$, and faithful flatness transports its characteristic upwards. It is used in the spreading step that produces faithfully flat algebras with canonical polarisation data in the Cherednik–Drinfeld setting for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FiniteType_exists_prime_charP_residueField_of_isMaximal_of_faithfullyFlat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.FiniteType.exists_prime_charP_residueField_of_isMaximal_of_faithfullyFlat
    {S : Type} [CommRing S] [Algebra.FiniteType ℤ S] (𝔭 : PrimeSpectrum S) (h𝔪 : 𝔭.asIdeal.IsMaximal)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra S R] [Algebra (Localization.AtPrime 𝔭.asIdeal) R]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) R]
    (hff : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) R) :
    ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField R) p := by sorry
