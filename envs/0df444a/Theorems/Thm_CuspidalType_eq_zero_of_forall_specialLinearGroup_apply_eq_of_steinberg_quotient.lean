-- Prove2me | Theorems.Thm_CuspidalType_eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient
-- name    : CuspidalType.eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/5211e462-45ae-5137-88c6-e9fe91f88a8c
-- title:
--   No SL₂(𝔽_q)-invariants in Steinberg modulo constants
-- statement:
--   Let $q$ be a prime, let $\kappa$ be a field with $q + 1 = 0$ in $\kappa$, and let $V$ be a finite-dimensional $\kappa$-vector space carrying a representation $\rho$ of $\mathrm{GL}_2(\mathbb{Z}/q)$, the group of invertible $2\times 2$ matrices over $\mathbb{Z}/q$. Write $\mathbb{P}^1 = \mathrm{Projectivization}(\mathbb{Z}/q, (\mathbb{Z}/q)^2)$ and let $\mathrm{ind}$ be the permutation representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on the finitely supported functions $\mathbb{P}^1 \to \kappa$, given by pushing forward supports along the action of $g$ on $\mathbb{P}^1$. Let $\mathrm{St}$ be the subrepresentation consisting of those $v$ with vanishing coefficient sum, i.e. the kernel of the linear combination map with all weights $1$, and let $\mathbf{1}$ be the function constantly equal to $1$ on $\mathbb{P}^1$. Assume given a $\kappa$-linear map $\pi \colon \mathrm{St} \to V$ which is equivariant, in the sense that $\pi(\mathrm{ind}(g)v) = \rho(g)\pi(v)$ for all $g$ and all $v \in \mathrm{St}$, which is surjective, and whose kernel is exactly the set of scalar multiples of $\mathbf{1}$: $\pi(v) = 0$ if and only if $v = c\mathbf{1}$ for some $c \in \kappa$. The conclusion is that every $v \in V$ satisfying $\rho(g)v = v$ for all $g$ in $\mathrm{SL}_2(\mathbb{Z}/q)$ (acting through the inclusion of $\mathrm{SL}_2$ into $\mathrm{GL}_2$) is zero.
--
--   The statement is the vanishing of $\mathrm{SL}_2(\mathbb{F}_q)$-invariants in the quotient of the Steinberg representation of $\mathrm{GL}_2(\mathbb{F}_q)$ by the constants, presented as a property of any equivariant surjection from $\mathrm{St}$ with kernel the line of constants. It is used in the analysis of eigensystems in the cohomology of $\Gamma_0$-type groups with coefficients in a cuspidal type, where it supplies the input that the relevant coefficient module has no non-zero invariants under $\mathrm{SL}_2(\mathbb{F}_q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspidalType.eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient
    (q : ℕ) [Fact q.Prime]
    (κ : Type) [Field κ] (hq1 : (q : κ) + 1 = 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ) :
    ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0 := by sorry
