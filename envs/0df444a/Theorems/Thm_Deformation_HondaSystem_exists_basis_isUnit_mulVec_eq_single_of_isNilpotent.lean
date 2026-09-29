-- Prove2me | Theorems.Thm_Deformation_HondaSystem_exists_basis_isUnit_mulVec_eq_single_of_isNilpotent
-- name    : Deformation.HondaSystem.exists_basis_isUnit_mulVec_eq_single_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/96c72c7d-b162-5d97-8085-5da7a8ab0ca2
-- title:
--   Linear-algebra core of Fontaine's normal form
-- statement:
--   Let $\mathcal O$ be a commutative ring and $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal O$, equipped with an $\mathcal O$-algebra structure on $\mathbb Z/p$ whose structure map $\mathcal O \to \mathbb Z/p$ has kernel exactly the ideal $(p)$, and assume $\mathcal O$ is adically complete with respect to $(p)$. Let $d$ be a natural number and let $L$ be a finite free $\mathcal O$-module with $\operatorname{rank}_{\mathcal O} L = d$. Let $\lambda_0, \lambda_1 \colon L \to (\mathbb Z/p)^{d}$ be $\mathcal O$-linear maps (the target being the module of functions on $\mathrm{Fin}\,d$) such that $\lambda_0$ is surjective and every $m \in L$ with $\lambda_0(m) = 0$ lies in the submodule $(p)\cdot L$; and suppose $\lambda_1 = C \cdot \lambda_0$ pointwise, where $C$ is a nilpotent $d \times d$ matrix over $\mathbb Z/p$ acting by matrix–vector multiplication. The assertion is the existence of a basis $b$ of $L$ indexed by $\mathrm{Fin}\,d$ and a matrix $P \in M_d(\mathcal O)$ which is a unit in the matrix ring, such that, writing $\bar P$ for the entrywise reduction of $P$ along $\mathcal O \to \mathbb Z/p$: for every $i$ one has $\bar P\,\lambda_0(b_i) = e_i$, the $i$-th standard basis vector, and for all $i, j$ with $j \le i$ the $j$-th coordinate of $\bar P\,\lambda_1(b_i)$ vanishes.
--
--   This is the purely linear-algebraic content of Fontaine's normal-form lemma for the Honda system of a unipotent $p$-divisible group: a flag basis for a nilpotent operator over the residue field, lifted to $\mathcal O$, simultaneously normalises the first covector component to the identity and makes the second strictly triangular. It is used in the construction of a basis putting the associated multivariate formal group law into normal form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_exists_basis_isUnit_mulVec_eq_single_of_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.HondaSystem.exists_basis_isUnit_mulVec_eq_single_of_isNilpotent
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (L : Type v) [AddCommGroup L] [Module 𝓞 L] [Module.Free 𝓞 L] [Module.Finite 𝓞 L]
    (hrank : Module.finrank 𝓞 L = d)
    (lam₀ lam₁ : L →ₗ[𝓞] (Fin d → ZMod p)) (hsurj : Function.Surjective lam₀)
    (hkerlam : ∀ m : L, lam₀ m = 0 → m ∈ Ideal.span {(p : 𝓞)} • (⊤ : Submodule 𝓞 L))
    (C : Matrix (Fin d) (Fin d) (ZMod p)) (hC : IsNilpotent C) (hlam₁ : ∀ m, lam₁ m = C.mulVec (lam₀ m)) :
    ∃ (b : Module.Basis (Fin d) 𝓞 L) (P : Matrix (Fin d) (Fin d) 𝓞), IsUnit P ∧
      (∀ i, (P.map (algebraMap 𝓞 (ZMod p))).mulVec (lam₀ (b i)) = Pi.single i 1) ∧
      (∀ i j : Fin d, j ≤ i → (P.map (algebraMap 𝓞 (ZMod p))).mulVec (lam₁ (b i)) j = 0) := by sorry
