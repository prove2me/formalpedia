-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_le_iSup_rightConv_eq_smul_of_finiteDimensional
-- name    : AutomorphicForm.CuspidalSpectrum.exists_le_iSup_rightConv_eq_smul_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/45799ab8-e099-5e4d-9d8a-5c3e47899596
-- title:
--   Eigenspace decomposition of right convolution on a finite-dimensional cut
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,\sigma,\alpha,\beta$ be reals, $T$ a finite set of elements of $\mathrm{GL}_2$ of the adeles of $F$, $\xi$ a character of the full idele unit group with $\|\xi(z)\|=\|z\|^{\sigma}$ for all $z$ (the predicate `HasModulus`), $N$ an ideal of $\mathcal{O}_F$, `tys` an archimedean type family, and $V$ a $\mathbb{C}$-submodule of functions on $\mathrm{GL}_2$ of the adeles. Write $X$ for the cut $V\cap\{\varphi : \varphi(gu)=\varphi(g)\text{ for all }g\text{ and all }u\in \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})\}\cap \mathrm{archCutSubmodule}(\mathrm{tys})$, the last factor being $\bigcap_{w}\sum_{i}$ of the type submodules $\mathrm{archTypeSubmoduleAt}(w,\mathrm{tys.rep}\,w\,i)$ over the infinite places $w$ (the level condition is read off the production pins attached to the window $\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}(c,u,d_1,d_2)\}$, the level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators `heckeGen`, and the box `adelicBox`). Assume $\Phi_0$ is a slab fundamental domain for the parameters $\alpha,\beta$, that $X$ is contained in the space of continuous smooth cuspidal automorphic functions with central character $\xi$ on $\Phi_0$, that $X$ is finite-dimensional over $\mathbb{C}$, and that $f$ is a factorizable test function with $f(y)=\overline{f(y^{-1})}\,\|\det y\|^{-\sigma}$ such that right convolution $\varphi\mapsto\big(g\mapsto\int \varphi(gx)f(x)\,dx\big)$ against the adelic Haar measure maps $X$ into $X$ and vanishes on no non-zero element of $X$. Then there are $n\in\mathbb{N}$, non-zero scalars $\lambda_1,\dots,\lambda_n\in\mathbb{C}$ and submodules $E_1,\dots,E_n$ of the function space with each $E_i\subseteq X$, with $\varphi * f=\lambda_i\varphi$ for every $\varphi\in E_i$, and with $X\subseteq \sum_i E_i$.
--
--   This is the linear-algebraic endpoint of the eigen-capture argument for cuspidal constituents of $\mathrm{GL}_2$ over a number field: the convolution operator is realised as a compact symmetric operator on the cusp subcarrier attached to the slab fundamental domain, and on a finite-dimensional invariant cut it therefore splits into finitely many eigen-slices, whose eigenvalues are non-zero by injectivity. It feeds the decomposition statement [`AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule`](thm.html#AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_le_iSup_rightConv_eq_smul_of_finiteDimensional.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_le_iSup_rightConv_eq_smul_of_finiteDimensional
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (hXc : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hfin : FiniteDimensional ℂ ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hflat : flat F σ f = f)
    (hpres : ∀ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys, rightConv F φ f ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys)
    (hinj : ∀ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys, rightConv F φ f = 0 → φ = 0) :
    ∃ (n : ℕ) (lam : Fin n → ℂ) (_ : ∀ i, lam i ≠ 0) (E : Fin n → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ i, E i ≤ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ∧ ∀ φ ∈ E i, rightConv F φ f = lam i • φ) ∧
      V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ ⨆ i, E i := by sorry
