-- Prove2me | Theorems.Thm_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent
-- name    : Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/8ca1629e-b71b-5b71-8293-93d25484ccca
-- title:
--   Free Dieudonné cover of a nilpotent Dieudonné datum
-- statement:
--   Let $A$ be a commutative ring, let $\ell \in A$, and let $D$ be an $A$-module that is finite as an $A$-module (i.e. finitely generated). Let $M$ be a Dieudonné datum for $\ell$ on $D$, that is, a pair of $A$-linear endomorphisms $F = M.F$ and $V = M.V$ of $D$ with $F \circ V = \ell \cdot \mathrm{id}_D$ and $V \circ F = \ell \cdot \mathrm{id}_D$, and assume that both $F$ and $V$ are nilpotent endomorphisms. Then there exist natural numbers $r$, $N$, $k$, a Dieudonné datum $M_1$ for the same $\ell$ on the free module $A^r$ (indexed by `Fin r`), consisting of $A$-linear endomorphisms $F_1 = M_1.F$ and $V_1 = M_1.V$ with $F_1 \circ V_1 = V_1 \circ F_1 = \ell \cdot \mathrm{id}$, and an $A$-linear map $\pi : A^r \to D$ such that: $\pi$ is surjective; $\pi \circ F_1 = F \circ \pi$ and $\pi \circ V_1 = V \circ \pi$, so that $\pi$ is a morphism of Dieudonné data; and $k > 0$ together with $F_1^N = \ell^k \cdot \mathrm{id}$ and $V_1^N = \ell^k \cdot \mathrm{id}$. Only $k$ is asserted to be positive; no lower bound on $r$ or $N$ is claimed.
--
--   This is the construction of a finite free Dieudonné cover of a finitely generated Dieudonné datum with nilpotent $F$ and $V$, the first step in Fontaine's resolution of such a module by free modules carrying $\ell$-adically topologically nilpotent $F$ and $V$ (the conditions $F_1^N = V_1^N = \ell^k \cdot \mathrm{id}$ with $k > 0$ encode that nilpotence, and force $F_1$, $V_1$ to be injective when $\ell$ is a non-zero-divisor). It is used by [`Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent_V`](thm.html#Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent_V).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneDatum_exists_free_cover_of_isNilpotent.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.DieudonneDatum.exists_free_cover_of_isNilpotent
    {A : Type u} [CommRing A] {ℓ : A} {D : Type v} [AddCommGroup D] [Module A D]
    [Module.Finite A D] (M : Deformation.DieudonneDatum ℓ D)
    (hF : IsNilpotent M.F) (hV : IsNilpotent M.V) :
    ∃ (r N k : ℕ) (M₁ : Deformation.DieudonneDatum ℓ (Fin r → A)) (π : (Fin r → A) →ₗ[A] D),
      Function.Surjective π ∧ π ∘ₗ M₁.F = M.F ∘ₗ π ∧ π ∘ₗ M₁.V = M.V ∘ₗ π ∧
      0 < k ∧ M₁.F ^ N = ℓ ^ k • LinearMap.id ∧ M₁.V ^ N = ℓ ^ k • LinearMap.id := by sorry
