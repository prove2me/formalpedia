-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
-- name    : AutomorphicForm.CuspidalSpectrum.map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/0a4b09d0-152e-5157-bde5-39fddddbc214
-- title:
--   Spectral dichotomy for a typed level cut in an irreducible cuspidal subrepresentation
-- statement:
--   Let $F$ be a number field, let $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_F)$ be a slab fundamental domain for the global points in the determinant-norm slab $[\alpha,\beta]$ (so $0<\alpha<\beta$), let $\sigma\in\mathbb{R}$ and let $\xi$ be a character of the full idele unit group with $\|\xi(z)\|=\|z\|^{\sigma}$ for all $z$. Let $M$ be a submodule of the cuspidal subcarrier $\mathcal H=$ `cuspSubcarrier F hΦ₀ σ ξ` (the closure in $L^2$ of the weighted measure of the image of the continuous cuspidal automorphic members) which is irreducible in the sense of `IsIrreducibleCuspSubrep`: closed, invariant under all continuous lifts of right translations by finite adelic elements and by archimedean row isometries and of right convolution by factorizable archimedean-bi-finite test functions, nonzero, and admitting no proper nonzero closed subrepresentation. Let $U=O\sqcap\ker(\mathrm{glArch})$ be compact with $O$ a subgroup that is open, let $\tau_w$ be an archimedean representation datum with irreducible $\rho$ at each infinite place $w$, and let $f$ be a factorizable test function on $\mathrm{GL}_2(\mathbb{A}_F)$ which is level-spherical of type $(\tau_w)_w$ at $U$, i.e. $f(g)=f_\infty(g_\infty)\mathbf 1_{\mathrm{glFin}(U)}(g_{\mathrm{fin}})$ with $f_\infty$ a compactly supported smooth archimedean factor, bi-finite of that type and invariant under conjugation by archimedean row isometries, and which satisfies $\mathrm{flat}_\sigma f=f$. Let $T$ be a continuous endomorphism of $\mathcal H$ whose underlying linear map is symmetric and which implements right convolution by $f$ on classes of continuous cuspidal members $\varphi$ with $\varphi * f$ again such a member. Let $Y$ be a submodule of complex functions on $\mathrm{GL}_2(\mathbb{A}_F)$ consisting of continuous cuspidal automorphic members for $(\Phi_0,\xi)$ whose classes lie in $M$, invariant under right translation by $U$, and contained in the $\tau$-type cut (the intersection over all infinite places $w$ of the $\tau_w$-isotypic submodule). Then for every real $r>0$, writing $H_r=\bigsqcup_{\|\mu\|\ge r}\ker(T-\mu)$ for the supremum of the eigenspaces of $T$ with eigenvalue of norm at least $r$, the image $\widetilde Y$ of all of $Y$ in $\mathcal H$ satisfies either $\widetilde Y\sqcap H_r^{\perp}=0$ or $\widetilde Y\subseteq H_r^{\perp}$.
--
--   This is the Hilbert-space form of the all-or-nothing alternative used in the spectral analysis of cusp forms: the high-eigenvalue part of a symmetric convolution operator either misses the typed level cut of an irreducible closed cuspidal subrepresentation entirely or swallows it. It feeds the finite-dimensionality statement [`AutomorphicForm.CuspidalSpectrum.finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep`](thm.html#AutomorphicForm.CuspidalSpectrum.finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep), on the way to admissibility of cuspidal representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) U f)
    (hflat : flat F σ f = f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hsymm : (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)).IsSymmetric)
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYc : Y ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hYM : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ Y), toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hYc hψ⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F))
    (r : ℝ) (hr : 0 < r) :
    Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ⊓
        (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ = ⊥ ∨
      Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ≤
        (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (Tc : Module.End ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) μ)ᗮ := by sorry
