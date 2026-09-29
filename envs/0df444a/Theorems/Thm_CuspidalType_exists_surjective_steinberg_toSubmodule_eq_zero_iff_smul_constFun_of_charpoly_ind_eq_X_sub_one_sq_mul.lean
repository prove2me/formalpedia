-- Prove2me | Theorems.Thm_CuspidalType_exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul
-- name    : CuspidalType.exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/9e8a2cd7-91a0-5c60-8591-aa62e14f27c2
-- title:
--   Recognising ρ as Steinberg modulo constants from characteristic polynomials
-- statement:
--   Let $q$ be a prime, let $p$ be a prime with $p \neq 2$, and let $\kappa$ be a field of characteristic $p$. Write $\mathrm{GL}_2(\mathbb{Z}/q)$ for the general linear group of $2 \times 2$ matrices over $\mathbb{Z}/q$, and $\mathbb{P}^1$ for the projectivization of $(\mathbb{Z}/q)^2$; let $\mathrm{ind}$ denote the permutation representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on the finitely supported $\kappa$-valued functions on $\mathbb{P}^1$, given by pushforward along $v \mapsto g \cdot v$. Let $V$ be a finite-dimensional $\kappa$-vector space and $\rho$ a representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V$ such that for every $g$ the characteristic polynomial of $\mathrm{ind}(g)$ equals $(X-1)^2$ times the characteristic polynomial of $\rho(g)$. Then there is a $\kappa$-linear map $\pi$ from the submodule of functions whose coefficient sum (the $\kappa$-linear combination of all values with coefficients $1$) vanishes into $V$, such that $\pi$ is equivariant, i.e. $\pi(\mathrm{ind}(g)v) = \rho(g)\pi(v)$ for all $g$ and all $v$ in that submodule (which $\mathrm{ind}(g)$ preserves), $\pi$ is surjective, and $\pi(v) = 0$ holds precisely when $v$ is a scalar multiple of the all-ones function on $\mathbb{P}^1$.
--
--   This identifies any representation with the stated characteristic-polynomial factorisation as the quotient of the mod $p$ Steinberg representation of $\mathrm{GL}_2(\mathbb{F}_q)$ (the coefficient-sum-zero part of the permutation representation on $\mathbb{P}^1(\mathbb{F}_q)$) by the line of constant functions, a recognition statement of Brauer–Nesbitt type. It is used in the analysis of the local behaviour at $q$ of the representation attached to a semistable Weierstrass model, where the Steinberg quotient appears in the eigensystem computation on $H^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem
CuspidalType.exists_surjective_steinberg_toSubmodule_eq_zero_iff_smul_constFun_of_charpoly_ind_eq_X_sub_one_sq_mul
    {q : ℕ} [Fact q.Prime] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (κ : Type) [Field κ] [CharP κ p]
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] (ρ : Representation κ (CuspidalType.GL2 q) V)
    (hρ : ∀ g : CuspidalType.GL2 q,
      LinearMap.charpoly (CuspidalType.ind q κ g) = (X - 1) ^ 2 * LinearMap.charpoly (ρ g)) :
    ∃ π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V,
      (∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v)) ∧
      Function.Surjective π ∧
      ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ := by sorry
