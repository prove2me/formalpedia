-- Prove2me | Theorems.Thm_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent_V
-- name    : Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent_V
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/5ff906ce-af88-5753-84ef-6ec69f0fd878
-- title:
--   Free Dieudonné cover with injective, topologically nilpotent V
-- statement:
--   Let $A$ be a commutative ring that is a domain and a discrete valuation ring, and let $\ell \in A$ be an element generating the maximal ideal of $A$, so $\ell$ is a uniformiser. Let $D$ be an $A$-module that is both Noetherian and Artinian, i.e. of finite length, and let $M$ be a Dieudonné datum with parameter $\ell$ on $D$: a pair of $A$-linear endomorphisms $F = M.F$ and $V = M.V$ of $D$ with $F \circ V = \ell \cdot \mathrm{id}$ and $V \circ F = \ell \cdot \mathrm{id}$. Assume $V$ is nilpotent (no nilpotence is required of $F$). Then there exist natural numbers $r$ and $N$, a Dieudonné datum $M_1$ with the same parameter $\ell$ on the free module $\mathrm{Fin}\,r \to A \cong A^r$, with structure maps $F_1 = M_1.F$ and $V_1 = M_1.V$, and an $A$-linear map $\pi \colon A^r \to D$ such that: $\pi$ is surjective; $\pi$ intertwines the two data, i.e. $F_1$ followed by $\pi$ equals $\pi$ followed by $F$, and likewise $V_1$ followed by $\pi$ equals $\pi$ followed by $V$; every element of the image of $V_1^N$ is of the form $\ell \cdot y$ for some $y \in A^r$, that is $V_1^N(A^r) \subseteq \ell A^r$; and $V_1$ is injective.
--
--   This is the step, in Fontaine's and Conrad's treatment of finite group schemes and Honda systems, which presents a finite-length Dieudonné module with nilpotent Verschiebung as an equivariant quotient of a free Dieudonné module of "unipotent $p$-divisible type", where $V$ is injective and topologically nilpotent in the sense that some power of it lands in $\ell A^r$. It relaxes the bi-nilpotence hypothesis of [`Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent`](thm.html#Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent), which it cites, at the cost of the weaker conclusion on powers of $V_1$, and it feeds the construction of free resolutions in [`Deformation.HondaSystem.exists_free_resolution_of_isNilpotent`](thm.html#Deformation.HondaSystem.exists_free_resolution_of_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent_V.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent_V
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ℓ : A}
    (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ})
    {D : Type v} [AddCommGroup D] [Module A D] [IsNoetherian A D] [IsArtinian A D]
    (M : Deformation.DieudonneDatum ℓ D) (hV : IsNilpotent M.V) :
    ∃ (r N : ℕ) (M₁ : Deformation.DieudonneDatum ℓ (Fin r → A)) (π : (Fin r → A) →ₗ[A] D),
      Function.Surjective π ∧ π ∘ₗ M₁.F = M.F ∘ₗ π ∧ π ∘ₗ M₁.V = M.V ∘ₗ π ∧
      (∀ x, ∃ y, (M₁.V ^ N) x = ℓ • y) ∧ Function.Injective M₁.V := by sorry
