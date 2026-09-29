-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialModule_exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit
-- name    : CerednikDrinfeld.SpecialModule.exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/01b5f6e4-1c65-5444-97ef-f96953b9947d
-- title:
--   Two-dimensional Λ-modules are standard away from qq'
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb{Q}$ be such that $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for each height-one prime $v$ of the integers of $\mathbb{Q}$ the completion $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element a unit) exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule that is a maximal order: it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and every order containing it equals it. Let $\mu\in\Lambda$ satisfy $\mu^2=-(qq')\cdot 1$, and let $\mathrm{star}\colon\Lambda\to\Lambda$ be any map with $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x\in\Lambda$. Let $k$ be an algebraically closed field in which $qq'$ is a unit, $W$ a finite-dimensional $k$-space with $\dim_k W=2$, and $\Psi\colon\Lambda\to\operatorname{End}_k(W)$ additive, with $\Psi(1)=\mathrm{id}$ and $\Psi(xy)=\Psi(x)\circ\Psi(y)$ whenever $xy\in\Lambda$. Then there exist $\theta\colon\Lambda\to M_2(k)$ and a $k$-linear isomorphism $e\colon W\to k^2$ with $e(\Psi(x)w)=\theta(x)\,e(w)$, such that $\theta$ is additive, $\theta(1)=1$, $\theta(xy)=\theta(x)\theta(y)$ for $xy\in\Lambda$, the $k$-span of the image of $\theta$ is all of $M_2(k)$, $\theta(\mathrm{star}(x))=\theta(\mu)^{-1}\operatorname{adj}(\theta(x))\,\theta(\mu)$, $\operatorname{tr}\theta(\mu)=0$, $\det\theta(\mu)=qq'$ in $k$, and $\operatorname{tr}\theta(x)=n$ in $k$ whenever $x+\bar{x}=n\in\mathbb{Z}$.
--
--   This is the pointwise linear algebra behind the splitting of a maximal order in an indefinite quaternion algebra at a place away from its discriminant: any unital two-dimensional module over $\Lambda$ over an algebraically closed field in which $qq'$ is invertible is the standard $M_2(k)$-module, with the involution $x\mapsto x^{\star}$ becoming the $\theta(\mu)$-twisted adjugate and the reduced trace becoming the matrix trace. It is used in the study of the special (Čerednik–Drinfeld) fibre of fake elliptic curves, being cited by the two statements on the vanishing of balanced classes and on traces on primitives for fake elliptic curves in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialModule_exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.SpecialModule.exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (k : Type) [Field k] [IsAlgClosed k] (hqq : IsUnit ((q * q' : ℕ) : k))
    (W : Type) [AddCommGroup W] [Module k W] [Module.Finite k W] (hW : Module.finrank k W = 2)
    (Ψ : ↥Λ → (W →ₗ[k] W))
    (hΨ_add : ∀ x y : ↥Λ, Ψ (x + y) = Ψ x + Ψ y)
    (hΨ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, Ψ ⟨1, h1⟩ = LinearMap.id)
    (hΨ_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      Ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = Ψ x ∘ₗ Ψ y) :
    ∃ (θ : ↥Λ → Matrix (Fin 2) (Fin 2) k) (e : W ≃ₗ[k] (Fin 2 → k)),
      (∀ (x : ↥Λ) (w : W), e (Ψ x w) = (θ x).mulVec (e w)) ∧
      (∀ x y : ↥Λ, θ (x + y) = θ x + θ y) ∧
      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, θ ⟨1, h1⟩ = 1) ∧
      (∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        θ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = θ x * θ y) ∧
      (∀ m : Matrix (Fin 2) (Fin 2) k, m ∈ Submodule.span k (Set.range θ)) ∧
      (∀ x : ↥Λ, θ (star x) = (θ μ)⁻¹ * (θ x).adjugate * θ μ) ∧
      (θ μ).trace = 0 ∧ (θ μ).det = ((q * q' : ℕ) : k) ∧
      (∀ (x : ↥Λ) (n : ℤ), (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        (θ x).trace = (n : k)) := by sorry
