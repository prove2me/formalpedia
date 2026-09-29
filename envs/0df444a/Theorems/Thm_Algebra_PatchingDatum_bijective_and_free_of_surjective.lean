-- Prove2me | Theorems.Thm_Algebra_PatchingDatum_bijective_and_free_of_surjective
-- name    : Algebra.PatchingDatum.bijective_and_free_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/f88ac091-92a4-5ad8-a0a8-02a70326be28
-- title:
--   Patching exit: R ≅ T, M free, T a power-series quotient
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation domain (complete for the adic topology of its maximal ideal) with finite residue field, let $\ell, r$ be natural numbers with the image of $\ell$ in $\mathcal O$ lying in the maximal ideal, let $R$ be a commutative $\mathcal O$-algebra and $M$ a nonzero $R$-module. Assume given a patching datum $P$ for $(R,M)$ in $r$ variables with exponent $\ell$, i.e. for every $n$ a patching level relative to the ideal $J_n = ((1+X_j)^{\ell^n}-1 : j \in \mathrm{Fin}\, r)$ of $\mathcal O[[X_1,\dots,X_r]]$: a module $N$ over the power-series ring, an $\mathcal O$-algebra endomorphism $\varphi$ of it, a surjective $\mathcal O$-algebra map $\psi$ onto $R$ killing each $\varphi(X_i)$, a surjection $\pi : N \to M$ of abelian groups that is semilinear along $\psi$ and whose kernel is exactly $(\varphi(X_1),\dots,\varphi(X_r))N$, together with $d$ elements $b_i$ of $N$ whose $\varphi$-twisted combinations exhaust $N$ and satisfy $\sum_i \varphi(c_i) b_i = 0$ precisely when all $c_i \in J_n$. Let further $T$ be a commutative $\mathcal O$-algebra equipped with a $T$-module structure on the same $M$, and let $R \to T$ be a surjective $\mathcal O$-algebra homomorphism such that the $T$-action of the image of $x \in R$ on $M$ agrees with the $R$-action of $x$. Then $R \to T$ is bijective, $M$ is free both as an $R$-module and as a $T$-module, the annihilator of $M$ in $R$ is the zero ideal, and there exist $f_1,\dots,f_r \in \mathcal O[[X_1,\dots,X_r]]$ together with an $\mathcal O$-algebra isomorphism $\mathcal O[[X_1,\dots,X_r]]/(f_1,\dots,f_r) \cong T$.
--
--   This is the form in which the Taylor–Wiles–Diamond patching argument is used: from an abstract patching datum for a module $M$ over $R$ and a compatible surjection of $R$ onto a second $\mathcal O$-algebra $T$ acting on $M$, one gets that the surjection is an isomorphism, that $M$ is free and faithful, and that $T$ is a quotient of a power-series ring in $r$ variables by $r$ relations. It is invoked in the passage from deformation-ring data and Hecke-algebra data to the conclusions $R = T$, freeness and the complete-intersection presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean

import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.PatchingDatum.bijective_and_free_of_surjective
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ℓ r : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (P : Algebra.PatchingDatum 𝒪 ℓ r R M)
    {T : Type} [CommRing T] [Algebra 𝒪 T] [Module T M]
    (RtoT : R →ₐ[𝒪] T) (hsurj : Function.Surjective RtoT)
    (hcompat : ∀ (x : R) (m : M), RtoT x • m = x • m) :
    Function.Bijective RtoT ∧ Module.Free R M ∧ Module.Free T M ∧
      Module.annihilator R M = ⊥ ∧
      ∃ f : Fin r → MvPowerSeries (Fin r) 𝒪,
        Nonempty ((MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) := by sorry
