-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
-- name    : AutomorphicForm.CuspidalSpectrum.exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/a0a252b2-6ac3-5619-94c7-9ef409abd02b
-- title:
--   Non-zero convolution eigenvectors come from continuous cusp forms
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb R$ and let $\Phi_0\subseteq\mathrm{GL}_2(\mathbb A_F)$ satisfy `IsSlabFundamentalDomain F α β Φ₀`, i.e. $0<\alpha<\beta$, $\Phi_0$ is contained in the slab of $g$ with idelic determinant norm in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on that slab with the restricted adelic Haar measure. Let $\sigma\in\mathbb R$, let $\xi$ be a homomorphism from the full subgroup of $(\mathbb A_F)^\times$ to $\mathbb C^\times$ with $\|\xi(z)\|=\|z\|^\sigma$ for all $z$, and let $f:\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ be a factorizable test function, that is, $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean and a finite test factor. Write $V$ for the submodule `cuspMemberSubmodule F Φ₀ ξ` of continuous functions that are smooth cuspidal automorphic for the pins attached to $\Phi_0$ with central character $\xi$, and $\mathcal H=$ `cuspSubcarrier F hΦ₀ σ ξ` for the closure in $L^2$ of the weighted measure of the image of $V$ under the class map `toCuspSubcarrier F hΦ₀ σ ξ`. Let $T_c$ be a continuous linear endomorphism of $\mathcal H$ such that for every $\varphi\in V$ whose right convolution $\varphi*f$, given by $g\mapsto\int\varphi(gx)f(x)\,dx$, again lies in $V$, one has $T_c[\varphi]=[\varphi*f]$. Let $\mu\neq0$ and $v\in\mathcal H$ with $T_cv=\mu v$. Then there exists $\psi\in V$ with $[\psi]=v$ and $\psi*f=\mu\,\psi$ as functions on $\mathrm{GL}_2(\mathbb A_F)$.
--
--   This is the regularity step in the spectral decomposition of the cuspidal spectrum of $\mathrm{GL}_2$ over a number field: an $L^2$-eigenvector of a convolution (smoothing) operator at a non-zero eigenvalue is the class of a genuine continuous cusp form satisfying the convolution equation pointwise. It is used in the construction of cuspidal constituents and in the production of non-zero $K$-finite vectors inside closed cuspidal subrepresentations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_mem_cuspMemberSubmodule_toCuspSubcarrier_eq_rightConv_eq_smul
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (μ : ℂ) (hμ : μ ≠ 0) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : Tc v = μ • v) :
    ∃ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ),
      toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ = v ∧ rightConv F ψ f = μ • ψ := by sorry
