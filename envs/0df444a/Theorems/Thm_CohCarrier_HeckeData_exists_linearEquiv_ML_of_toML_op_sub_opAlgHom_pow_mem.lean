-- Prove2me | Theorems.Thm_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
-- name    : CohCarrier.HeckeData.exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/e4120c42-c7f5-59db-81a4-ebc39a014aee
-- title:
--   Adjoining a residually redundant Hecke operator preserves the localisation
-- statement:
--   Let $\mathcal{O}$ be a Noetherian local ring, complete with respect to its maximal ideal, let $k$ be a field that is an $\mathcal{O}$-algebra with $\mathcal{O} \to k$ surjective, and let $V$ be a finitely generated $\mathcal{O}$-module. Let $DV$ and $DE$ be two pieces of Hecke data for $(\mathcal{O}, V, k)$, each consisting of an index type of generators, a family of pairwise commuting $\mathcal{O}$-linear endomorphisms of $V$ indexed by it, and residual values in $k$; for such data the free algebra is the polynomial algebra $\mathcal{O}[X_g]$ on the generators, `thetaTilde` is the evaluation $\mathcal{O}[X_g] \to k$ at the residual values, `mTheta` its kernel, `opAlgHom` the map $\mathcal{O}[X_g] \to \operatorname{End}_{\mathcal{O}}(V)$ sending $X_g$ to the corresponding operator, and `ML` the localisation of $V$ (as a module over the polynomial algebra, via `opAlgHom`) at the complement of `mTheta`, with `toML` the canonical map $V \to$ `ML`. Assume given a bijection $\sigma$ of $DV.\mathrm{Gen} \sqcup \{*\}$ with $DE.\mathrm{Gen}$ matching, for each old generator $g$, both the operator and the residual value of $\sigma(g)$ with those of $g$; a polynomial $z_0 \in \mathcal{O}[X_g]$ over $DV$'s generators whose value under `thetaTilde` for $DV$ equals the residual value of $DE$ at the extra generator $\sigma(*)$; and a natural number $n$ such that for every $v \in V$ the image under $DV$'s `toML` of $(Z - z_0(X))^n v$, where $Z$ is $DE$'s operator at $\sigma(*)$, lies in $\mathfrak{m}_{\mathcal{O}} \cdot DV.\mathrm{ML}$. Then there exists an $\mathcal{O}$-linear isomorphism $e : DE.\mathrm{ML} \to DV.\mathrm{ML}$ with $e(X_{\sigma(g)} \cdot x) = X_g \cdot e(x)$ for every old generator $g$ and every $x \in DE.\mathrm{ML}$; no compatibility with the extra generator is asserted.
--
--   This is the comparison between the localisation of a Hecke module at a maximal ideal of an anemic Hecke algebra and its localisation at the corresponding maximal ideal of the algebra obtained by adjoining one further operator whose residual behaviour is already prescribed by the old ones — typically a diamond operator acting residually through the polynomial $z_0$ — as needed in the Taylor–Wiles patching argument. It is applied in [`CuspForm.TWLevel.exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq`](thm.html#CuspForm.TWLevel.exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq) to the diamond operators on the cohomology of the relevant modular curves; its proof cites the finiteness and freeness statement [`CohCarrier.HeckeData.finite_ML_and_free_ML`](thm.html#CohCarrier.HeckeData.finite_ML_and_free_ML) for these localisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.lean

import Mathlib
import Definitions.Def_CohCarrier_HeckeData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open CohCarrier

theorem CohCarrier.HeckeData.exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

    (DV DE : HeckeData 𝒪 V k) (σ : DV.Gen ⊕ Unit ≃ DE.Gen)
    (hop : ∀ g : DV.Gen, DE.op (σ (Sum.inl g)) = DV.op g)
    (hθ : ∀ g : DV.Gen, DE.θbar (σ (Sum.inl g)) = DV.θbar g)

    (z₀ : DV.FreeAlg) (hz : DE.θbar (σ (Sum.inr ())) = DV.thetaTilde z₀)

    (n : ℕ) (hnil : ∀ v : V, DV.toML (((DE.op (σ (Sum.inr ())) - DV.opAlgHom z₀) ^ n) v) ∈
      (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DV.ML)) :
    ∃ e : DE.ML ≃ₗ[𝒪] DV.ML, ∀ (g : DV.Gen) (x : DE.ML),
      e ((MvPolynomial.X (σ (Sum.inl g)) : DE.FreeAlg) • x) = (MvPolynomial.X g : DV.FreeAlg) • e x := by sorry
