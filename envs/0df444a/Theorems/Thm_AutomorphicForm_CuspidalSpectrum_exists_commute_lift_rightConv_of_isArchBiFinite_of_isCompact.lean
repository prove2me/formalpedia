-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact
-- name    : AutomorphicForm.CuspidalSpectrum.exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/05f0562e-1dbc-5546-a0f0-5f99fe0e9e29
-- title:
--   Commuting bounded lift of right convolution on the cuspidal subcarrier
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be reals and $\Phi_0$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ which is a slab fundamental domain: $0<\alpha<\beta$, $\Phi_0$ lies in the determinant-norm slab `detNormSlab F α β`, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on that slab for the restricted adelic Haar measure. Let $\sigma\in\mathbb{R}$ and let $\xi$ be a character of the full group of idele units into $\mathbb{C}^\times$ with $\|\xi(z)\|=\|z\|^{\sigma}$ for all $z$. Let $U$ be a compact subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ of the form $U=O\cap\ker(\mathrm{glArch})$ with $O$ open, let $\tau$ assign to each infinite place $w$ an `ArchRepAt F w` whose representation $(\tau w).\rho$ of the row-isometry subgroup at $w$ is irreducible, and write $\langle 1,\tau\rangle$ for the archimedean type family with a single constituent $\tau w$ at each $w$. Let $f$ be a factorizable test function (a product of an archimedean test factor and a finite test factor) which is moreover level-spherical of type $\langle 1,\tau\rangle$ at level $U$: $f(g)=f_\infty(g_\infty)\cdot\mathbf{1}_{U_{\mathrm{fin}}}(g_{\mathrm{fin}})$ with $f_\infty$ an archimedean test factor, bi-finite of type $\langle 1,\tau\rangle$ and invariant under conjugation by each row-isometry subgroup. Let $T_c$ be a bounded $\mathbb{C}$-linear operator on the cuspidal subcarrier — the topological closure, inside the carrier `Carrier F Φ₀ σ`, of the image of the continuous smooth cuspidal automorphic functions with character $\xi$ — such that $T_c$ sends the class of every cuspidal member $\varphi$ to the class of $\varphi * f$ whenever the latter is again such a member, where $(\varphi*f)(g)=\int \varphi(gx)f(x)\,dx$. Finally let $h$ be a factorizable test function satisfying `IsArchBiFinite F ⟨1,τ⟩ h` (the function $x\mapsto h(x^{-1})$ lies in the archimedean cut submodule of the type family and $h$ in its dual cut submodule) and bi-$U$-invariant: $h(u'x)=h(x)=h(xu')$ for all $x$ and $u'\in U$. Then there exists a bounded $\mathbb{C}$-linear operator $S$ on the cuspidal subcarrier with $S\circ T_c=T_c\circ S$ such that for every cuspidal member $\varphi$ the convolution $\varphi*h$ is again a cuspidal member and $S$ carries the class of $\varphi$ to the class of $\varphi*h$.
--
--   This supplies the commuting pair of operators needed on the cuspidal part of the adelic $\mathrm{GL}_2$ spectrum: convolution by a bi-$U$-invariant test function of archimedean type $\tau$ is realised as a bounded operator commuting with the smoothing operator attached to the level-spherical function $f$ of the same type. It is used in the dichotomy for irreducible cuspidal subrepresentations, namely in [`AutomorphicForm.CuspidalSpectrum.map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep`](thm.html#AutomorphicForm.CuspidalSpectrum.map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact
    (F : Type) [Field F] [NumberField F]
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) U f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h) (hbh : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ U, h (u' * x) = h x ∧ h (x * u') = h x) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ), S.comp Tc = Tc.comp S ∧
      ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), ∃ h' : rightConv F φ h ∈ cuspMemberSubmodule F Φ₀ ξ,
        S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ h, h'⟩ := by sorry
