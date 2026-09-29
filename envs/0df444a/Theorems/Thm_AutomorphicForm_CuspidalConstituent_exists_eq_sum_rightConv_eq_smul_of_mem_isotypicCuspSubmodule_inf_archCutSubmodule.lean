-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
-- name    : AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/1024d303-271d-5abc-aab8-241cc7f5d4be
-- title:
--   Finite eigenexpansion of isotypic cusp vectors under one test function
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\{g x : g\in \Sigma\}$, where $\Sigma=$ `centreCutSiegelSet` $F\,c\,u\,d_1\,d_2$ consists of those $g$ whose finite part is finitely integral, all of whose archimedean components have local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norms at every infinite place lie in $[d_1,d_2]$; assume `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ can be written as $\gamma g z\in D$ with $\gamma\in\mathrm{GL}_2(F)$ and $z$ a central idelic scalar. Work with the carrier pins `productionPinsOf` attached to $D$, with level groups $N\mapsto$ `levelOne` $N$ intersected with the kernel of the archimedean projection, Hecke generators `heckeGen`, the adelic Haar data and the box `adelicBox`; their central group is all of $(\mathbb{A}_F)^\times$, and $\xi$ is a homomorphism from it to $\mathbb{C}^\times$. Let $N\neq 0$ be an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, $\mathrm{tys}$ an archimedean type family (a finite list of archimedean representations at each infinite place), and $\Psi$ a Hecke eigensystem with values in $\mathbb{C}$. Let $\varphi$ lie in the intersection of `isotypicCuspSubmodule` (the $\mathbb{C}$-span of the functions satisfying `IsIsotypicCuspFormAt` for these data) with `archCutSubmodule` $=\bigsqcap_{w}\bigsqcup_{i}$ `archTypeSubmoduleAt` $w$ $(\mathrm{tys.rep}\,w\,i)$. Then there are a factorizable test function $f$, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with archimedean and finite factors of the prescribed kinds, an $n\in\mathbb{N}$, non-zero scalars $\lambda_1,\dots,\lambda_n$ and functions $\psi_1,\dots,\psi_n$, each again in that same intersection, such that $\psi_i * f=\lambda_i\psi_i$ for the right convolution $g\mapsto\int \psi_i(gx)f(x)\,d\mu(x)$ against adelic Haar measure, and $\varphi=\sum_{i=1}^n\psi_i$. The data $f,n,\lambda,\psi$ may depend on $\varphi$; no uniformity in $\varphi$ and no finite-dimensionality of the cut is asserted.
--
--   This is the working form of the discreteness and admissibility of the cuspidal spectrum in the adelic $\mathrm{GL}_2$ setting: every vector of the isotypic-and-archimedean-type cut decomposes into finitely many right-convolution eigenvectors, with non-zero eigenvalues, for a single pure-tensor test function. It is used by [`AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent`](thm.html#AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent), which exhibits the cut as contained in a supremum of cuspidal constituents, and by the class-sum growth estimate [`AutomorphicForm.ClassSumGrowth.exists_forall_le_classSum_of_classCarriesMass`](thm.html#AutomorphicForm.ClassSumGrowth.exists_forall_le_classSum_of_classCarriesMass).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_eq_sum_rightConv_eq_smul_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys) :
    ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (_ : IsFactorizableTestFn F f) (n : ℕ) (lam : Fin n → ℂ) (_ : ∀ i, lam i ≠ 0)
      (ψ : Fin n → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ i, ψ i ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ∧
        rightConv F (ψ i) f = lam i • ψ i) ∧
      φ = ∑ i, ψ i := by sorry
