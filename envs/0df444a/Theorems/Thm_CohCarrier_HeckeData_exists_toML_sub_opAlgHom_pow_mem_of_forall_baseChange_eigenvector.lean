-- Prove2me | Theorems.Thm_CohCarrier_HeckeData_exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector
-- name    : CohCarrier.HeckeData.exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/01971a5f-3c9d-59ec-b1b0-a076838b72de
-- title:
--   Residual nilpotence tested on simultaneous eigenvectors over K
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring, $k$ a field which is an $\mathcal{O}$-algebra such that the structure map $\mathcal{O} \to k$ is surjective, and $V$ a finite $\mathcal{O}$-module. Let $D$ be a Hecke datum for $(\mathcal{O},V,k)$, that is: a type $D.\mathrm{Gen}$ of generators, a family $\mathrm{op}(g) \in \operatorname{End}_{\mathcal{O}}(V)$ of pairwise commuting endomorphisms indexed by $g \in D.\mathrm{Gen}$, and prescribed residual values $\bar\theta(g) \in k$. Let $Z \in \operatorname{End}_{\mathcal{O}}(V)$ commute with every $\mathrm{op}(g)$, and let $z_0$ be an element of $D.\mathrm{FreeAlg} = \mathcal{O}[X_g : g \in D.\mathrm{Gen}]$ (a multivariate polynomial ring). Let $K$ be an algebraically closed field which is an algebra over both $\mathcal{O}$ and $k$, compatibly. Assume the testing hypothesis: for every $x \in K \otimes_{\mathcal{O}} V$ with $x \neq 0$ and every $b \in K$, if the base change of $\mathrm{op}(g)$ to $K$ satisfies $\mathrm{op}(g)_K x = \bar\theta(g) x$ for all $g$ (the image of $\bar\theta(g)$ in $K$), and $Z_K x = b x$, then $b$ is the image in $K$ of $\tilde\theta(z_0) \in k$, the value of $z_0$ under the $\mathcal{O}$-algebra map $X_g \mapsto \bar\theta(g)$. Then there exists $n \in \mathbb{N}$ such that for all $v \in V$ the image of $(Z - z_0(\mathrm{op}))^n v$ in $D.\mathrm{ML}$ lies in $\mathfrak{m}_{\mathcal{O}} \cdot D.\mathrm{ML}$. Here $z_0(\mathrm{op})$ is the image of $z_0$ under the $\mathcal{O}$-algebra map $D.\mathrm{FreeAlg} \to \operatorname{End}_{\mathcal{O}}(V)$ sending $X_g \mapsto \mathrm{op}(g)$, $V$ is viewed as a $D.\mathrm{FreeAlg}$-module through that map, and $D.\mathrm{ML}$ is the localisation of $V$ at the prime complement of $\mathfrak{m}_\theta = \ker \tilde\theta$, with $D.\mathrm{toML}$ the canonical localisation map.
--
--   This is the criterion by which one checks that a further commuting operator has a single residual eigenvalue on the localised Hecke module: it converts that statement into a statement about simultaneous eigenvectors for the residual eigenvalue system $\bar\theta$ in $K \otimes_{\mathcal{O}} V$, where Galois-theoretic input is available. It is used in the auxiliary-level step [`CuspForm.AuxLevel.exists_toML_heckeTL_sub_opAlgHom_pow_mem_of_prime_of_not_dvd`](thm.html#CuspForm.AuxLevel.exists_toML_heckeTL_sub_opAlgHom_pow_mem_of_prime_of_not_dvd), which in turn feeds the comparison of localised Hecke modules before and after adjoining a residually unipotent generator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_HeckeData_exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector.lean

import Mathlib
import Definitions.Def_CohCarrier_HeckeData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open CohCarrier
open scoped TensorProduct

theorem CohCarrier.HeckeData.exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    (D : HeckeData 𝒪 V k)

    (Z : Module.End 𝒪 V) (hZ : ∀ g : D.Gen, Z * D.op g = D.op g * Z) (z₀ : D.FreeAlg)

    (K : Type) [Field K] [IsAlgClosed K] [Algebra 𝒪 K] [Algebra k K] [IsScalarTower 𝒪 k K]

    (htest : ∀ (x : K ⊗[𝒪] V) (b : K), x ≠ 0 →
      (∀ g : D.Gen, (D.op g).baseChange K x = algebraMap k K (D.θbar g) • x) →
      Z.baseChange K x = b • x → b = algebraMap k K (D.thetaTilde z₀)) :
    ∃ n : ℕ, ∀ v : V,
      D.toML (((Z - D.opAlgHom z₀) ^ n) v) ∈
        (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 D.ML) := by sorry
