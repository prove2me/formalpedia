-- Prove2me | Theorems.Thm_Deformation_HondaSystem_exists_free_resolution_of_isNilpotent
-- name    : Deformation.HondaSystem.exists_free_resolution_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/9b4a0ac5-7ba6-506a-9f21-4f6473006f2c
-- title:
--   Free resolution of a finite Honda system with nilpotent V
-- statement:
--   Let $A$ be a discrete valuation ring (a commutative domain whose maximal ideal is principal) and let $\ell \in A$ generate its maximal ideal. Let $D$ be an $A$-module that is both Noetherian and Artinian, and let $H = (F, V, L)$ be a Honda system on $D$ with parameter $\ell$, that is: $A$-linear endomorphisms $F, V$ of $D$ with $F \circ V = V \circ F = \ell \cdot \mathrm{id}$, together with a submodule $L \subseteq D$ such that every element of $L \cap \operatorname{range} F$ is of the form $\ell \cdot y$ with $y \in L$, such that $\ell \cdot y \in \operatorname{range} F$ for all $y \in L$, such that $\operatorname{range} F + L = D$, and such that $V$ is injective on $L$. Assume $V$ is nilpotent. Then there are natural numbers $r, N$, two Honda systems $H_1, H_2$ with parameter $\ell$ on the free module $A^r = (\mathrm{Fin}\ r \to A)$, an $A$-linear map $\varphi \colon A^r \to A^r$ and an $A$-linear map $\pi \colon A^r \to D$ such that $\varphi$ is injective, $\pi$ is surjective, $\operatorname{range} \varphi = \ker \pi$, $\varphi$ commutes with the two $F$'s and the two $V$'s ($\varphi \circ H_2.F = H_1.F \circ \varphi$ and $\varphi \circ H_2.V = H_1.V \circ \varphi$), $\pi$ likewise intertwines $H_1.F, H_1.V$ with $H.F, H.V$, the image of $H_1.L$ under $\pi$ is $H.L$, the preimage of $H_1.L$ under $\varphi$ is $H_2.L$, and both $H_1.V^N$ and $H_2.V^N$ take every element of $A^r$ into $\ell A^r$.
--
--   This is the resolution of a finite Honda system with nilpotent Verschiebung by a short exact sequence of Honda systems on free modules with topologically nilpotent $V$, the fourth step in Fontaine's classification of finite commutative group schemes over a complete discrete valuation ring by Honda systems. It feeds the construction of a $p$-divisible tower realising a given finite Honda system as a kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_exists_free_resolution_of_isNilpotent.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.HondaSystem.exists_free_resolution_of_isNilpotent
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ℓ : A}
    (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ})
    {D : Type v} [AddCommGroup D] [Module A D] [IsNoetherian A D] [IsArtinian A D]
    (H : Deformation.HondaSystem ℓ D) (hV : IsNilpotent H.V) :
    ∃ (r N : ℕ) (H₁ H₂ : Deformation.HondaSystem ℓ (Fin r → A))
      (φ : (Fin r → A) →ₗ[A] (Fin r → A)) (π : (Fin r → A) →ₗ[A] D),
      Function.Injective φ ∧ Function.Surjective π ∧ LinearMap.range φ = LinearMap.ker π ∧
      φ ∘ₗ H₂.F = H₁.F ∘ₗ φ ∧ φ ∘ₗ H₂.V = H₁.V ∘ₗ φ ∧
      π ∘ₗ H₁.F = H.F ∘ₗ π ∧ π ∘ₗ H₁.V = H.V ∘ₗ π ∧
      Submodule.map π H₁.L = H.L ∧ Submodule.comap φ H₁.L = H₂.L ∧
      (∀ x, ∃ y, (H₁.V ^ N) x = ℓ • y) ∧ (∀ x, ∃ y, (H₂.V ^ N) x = ℓ • y) := by sorry
