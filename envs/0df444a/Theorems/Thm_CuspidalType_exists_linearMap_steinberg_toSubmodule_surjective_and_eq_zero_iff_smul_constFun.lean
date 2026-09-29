-- Prove2me | Theorems.Thm_CuspidalType_exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun
-- name    : CuspidalType.exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/88855281-dbd4-59c2-92de-5d0802aedf73
-- title:
--   Equivariant quotient of the Steinberg module by constant functions
-- statement:
--   Let $q$ be a prime and $\kappa$ a field. Write $G=\mathrm{GL}_2(\mathbb{Z}/q)$ ([`CuspidalType.GL2 q`](def/CuspidalType_IsCuspidalOfType.html#L19)), let $\mathbb{P}=\mathbb{P}(\ (\mathbb{Z}/q)^2\ )$ be the projectivization of $\mathrm{Fin}\,2\to\mathbb{Z}/q$ ([`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21)), and let $\mathrm{ind}$ be the permutation representation of $G$ on the finitely supported functions $\mathbb{P}\to_{0}\kappa$, given by pushforward of supports along $g\cdot(-)$. Inside it, [`CuspidalType.steinberg q κ`](def/CuspidalType_IsCuspidalOfType.html#L57) is the subrepresentation whose underlying submodule is the kernel of the coefficient-sum map $\sum_{x}v(x)$, and [`CuspidalType.constFun q κ`](def/CuspidalType_IsCuspidalOfType.html#L67) is the function with value $1$ at every point of $\mathbb{P}$. The theorem asserts the existence of a type $V$, carrying an additive commutative group structure, a $\kappa$-module structure and finite-dimensionality over $\kappa$, together with a representation $\rho$ of $G$ on $V$ and a $\kappa$-linear map $\pi$ from the Steinberg submodule to $V$, such that: for every $g\in G$ and every $v$ in the submodule, $\pi$ of the element $\mathrm{ind}(g)v$ (with its membership witness) equals $\rho(g)\,\pi(v)$; $\pi$ is surjective; and for $v$ in the submodule, $\pi(v)=0$ if and only if the underlying finsupp of $v$ equals $c\cdot\mathrm{constFun}$ for some $c\in\kappa$.
--
--   This packages the Steinberg representation of $\mathrm{GL}_2(\mathbb{F}_q)$ over an arbitrary coefficient field as a finite-dimensional equivariant quotient in which exactly the scalar multiples of the constant function die; when $q+1\neq 0$ in $\kappa$ the constant function is not in the Steinberg submodule and $\pi$ is injective, while when $q+1=0$ it divides out the trivial line. It is used in the treatment of cuspidal type and of Hecke eigensystems attached to semistable models, via [`HeckeEis.isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP`](thm.html#HeckeEis.isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP) and [`WeierstrassCurve.exists_charP_rep_steinberg_quotient_isEigensystemH1_apOfModel_of_isSemistableModel_of_qCoeff_congr`](thm.html#WeierstrassCurve.exists_charP_rep_steinberg_quotient_isEigensystemH1_apOfModel_of_isSemistableModel_of_qCoeff_congr).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspidalType.exists_linearMap_steinberg_toSubmodule_surjective_and_eq_zero_iff_smul_constFun
    (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module κ V) (_ : FiniteDimensional κ V)
      (ρ : Representation κ (CuspidalType.GL2 q) V)
      (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V),
      (∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v)) ∧
      Function.Surjective π ∧
      (∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
        π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ) := by sorry
