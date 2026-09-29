-- Prove2me | Theorems.Thm_Algebra_PointDerivations_exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor
-- name    : Algebra.PointDerivations.exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/ff36e7c6-96ca-5489-991e-b81bbfdd403a
-- title:
--   Reading point-derivation-valued cocycles as tensors W ⊗ Hom(V^∨,H₁)
-- statement:
--   Let $\kappa$ be a field, $R$ a commutative $\kappa$-algebra with a ring homomorphism $\mathrm{ev}\colon R\to\kappa$, and $W$ a $\kappa$-vector space. For a $\kappa$-module $M$ write $\mathrm{PDer}(M)$ for the submodule of $\kappa$-linear maps $D\colon R\to M$ satisfying $D(ab)=\mathrm{ev}(a)\cdot D(b)+\mathrm{ev}(b)\cdot D(a)$; for $g\colon M\to M'$, [`Algebra.PointDerivations.map`](def/Algebra_PointDerivations.html#L47) sends $D$ to $g\circ D$. Assume given $\kappa$-linear isomorphisms $\Phi_M\colon \mathrm{PDer}(M)\cong W\otimes_\kappa M$ for every $\kappa$-module $M$, natural in the sense that $\Phi_{M'}(g\circ\delta)=(\mathrm{id}_W\otimes g)(\Phi_M\delta)$. Let $C_0\xrightarrow{d_0}C_1\xrightarrow{d_1}C_2$ be $\kappa$-linear maps, and $\mathrm{cls}_1\colon \ker d_1\to H_1$ a surjective $\kappa$-linear map with $\mathrm{cls}_1 z=0$ exactly when $z\in\mathrm{range}\,d_0$. Let $V$ be a finite-dimensional $\kappa$-space. Then there exists a function $\Psi\colon \mathrm{PDer}(\mathrm{Hom}_\kappa(V^\vee,C_1))\to W\otimes_\kappa \mathrm{Hom}_\kappa(V^\vee,H_1)$ such that: (i) every $c$ with $c(a)(\xi)\in\ker d_1$ for all $a\in R$, $\xi\in V^\vee$ admits $\hat c\in\mathrm{PDer}(\mathrm{Hom}_\kappa(V^\vee,\ker d_1))$ lifting it; (ii) for any such $c,\hat c$, $\Psi(c)=\Phi(\mathrm{cls}_1\circ\hat c)$, the postcomposition being `LinearMap.llcomp`; (iii) for such $c,c'$, $\Psi(c)=\Psi(c')$ iff $c(a)(\xi)-c'(a)(\xi)\in\mathrm{range}\,d_0$ for all $a,\xi$; (iv) $\Psi$ hits every element of $W\otimes_\kappa\mathrm{Hom}_\kappa(V^\vee,H_1)$ at some such $c$; (v) if $\varphi\colon V\to V$ is linear, $T$ satisfies $T(F)(\xi)=F(\xi\circ\varphi)$, $c$ is as above and $c'(a)(\xi)=c(a)(\xi\circ\varphi)$, then $\Psi(c')=(\mathrm{id}_W\otimes T)(\Psi(c))$.
--
--   This is the linear-algebra core of the Kodaira–Spencer style bookkeeping: it converts families of point derivations with values in $\mathrm{Hom}(V^\vee,C_1)$ into tensors over a cohomology group, with the cocycle-lifting, class-identification, cohomologous-equality, surjectivity and precomposition-equivariance properties packaged together. It is used in the construction of deformation classes over dual numbers for fake elliptic curves in the Cerednik–Drinfeld setting, where $C_\bullet$ is a Čech complex in degrees $0,1,2$ and $\Phi$ comes from a tangent-vector identification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_PointDerivations_exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor.lean

import Mathlib
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.PointDerivations.exists_reader_tensor_linearMap_dual_of_linearEquiv_tensor
    (κ : Type) [Field κ] (R : Type) [CommRing R] [Algebra κ R] (ev : R →+* κ)
    (W : Type) [AddCommGroup W] [Module κ W]
    (Φ : ∀ (M : Type) [AddCommGroup M] [Module κ M], ↥(Algebra.PointDerivations κ R ev M) ≃ₗ[κ] (W ⊗[κ] M))
    (hΦnat : ∀ (M M' : Type) [AddCommGroup M] [Module κ M] [AddCommGroup M'] [Module κ M'] (g : M →ₗ[κ] M')
        (δ : ↥(Algebra.PointDerivations κ R ev M)),
      Φ M' (Algebra.PointDerivations.map ev g δ) = _root_.TensorProduct.map (LinearMap.id : W →ₗ[κ] W) g (Φ M δ))
    {C₀ C₁ C₂ : Type} [AddCommGroup C₀] [Module κ C₀] [AddCommGroup C₁] [Module κ C₁] [AddCommGroup C₂] [Module κ C₂]
    (d₀ : C₀ →ₗ[κ] C₁) (d₁ : C₁ →ₗ[κ] C₂)
    (H₁ : Type) [AddCommGroup H₁] [Module κ H₁]
    (cls₁ : ↥(LinearMap.ker d₁) →ₗ[κ] H₁) (hcls₁ : Function.Surjective cls₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker d₁), cls₁ z = 0 ↔ (z : C₁) ∈ LinearMap.range d₀)
    (V : Type) [AddCommGroup V] [Module κ V] [Module.Finite κ V] :
    ∃ Ψ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)) → W ⊗[κ] (Module.Dual κ V →ₗ[κ] H₁),

      (∀ c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
        (∀ (a : R) (ξ : Module.Dual κ V), (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
        ∃ ĉ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))),
          ∀ (a : R) (ξ : Module.Dual κ V),
            (((ĉ : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))) a ξ : ↥(LinearMap.ker d₁)) : C₁) =
              (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ) ∧

      (∀ (c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)))
          (ĉ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))),
        (∀ (a : R) (ξ : Module.Dual κ V),
            (((ĉ : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁))) a ξ : ↥(LinearMap.ker d₁)) : C₁) =
              (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ) →
        Ψ c = Φ (Module.Dual κ V →ₗ[κ] H₁)
          (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker d₁)))
            (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker d₁) H₁ cls₁) ĉ)) ∧

      (∀ c c' : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
        (∀ (a : R) (ξ : Module.Dual κ V), (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
        (∀ (a : R) (ξ : Module.Dual κ V), (c' : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
        (Ψ c = Ψ c' ↔
          ∀ (a : R) (ξ : Module.Dual κ V), ∃ b : C₀,
            d₀ b = (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ - (c' : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ)) ∧

      (∀ w : W ⊗[κ] (Module.Dual κ V →ₗ[κ] H₁),
        ∃ c : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁)),
          (∀ (a : R) (ξ : Module.Dual κ V), (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) ∧ Ψ c = w) ∧

      (∀ (c c' : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] C₁))) (φ : V →ₗ[κ] V)
          (T : (Module.Dual κ V →ₗ[κ] H₁) →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁)),
        (∀ (F : Module.Dual κ V →ₗ[κ] H₁) (ξ : Module.Dual κ V), T F ξ = F (ξ ∘ₗ φ)) →
        (∀ (a : R) (ξ : Module.Dual κ V), (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ ∈ LinearMap.ker d₁) →
        (∀ (a : R) (ξ : Module.Dual κ V),
            (c' : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a ξ = (c : R →ₗ[κ] (Module.Dual κ V →ₗ[κ] C₁)) a (ξ ∘ₗ φ)) →
        Ψ c' = _root_.TensorProduct.map (LinearMap.id : W →ₗ[κ] W) T (Ψ c)) := by sorry
