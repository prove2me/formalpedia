-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType_principal
-- name    : AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/4a1aca38-40b2-5e35-9d83-1b98534267bb
-- title:
--   Real scalar action of a flat-symmetric level-spherical convolution
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $\mathfrak S$ for the centre-cut Siegel set of parameters $c,u,d_1,d_2$, namely the $g$ whose finite part lies in $\mathrm{GL}_2(\widehat{\mathcal O}_F)$ and whose archimedean component at every infinite place $w$ has local height $\ge c$, window invariant $\mathrm{xWindowSq}\le u^2$ and $\|\det\|_w \in [d_1,d_2]$; assume the union $D=\bigcup_{x\in T}\mathfrak S x$ covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g z\in D$. Let $\xi$ be a character of the full idele unit group with $|\xi(z)|=\|z\|^{\sigma}$ for a real $\sigma$, let $N\neq 0$ be an ideal of $\mathcal O_F$, and let $\tau$ assign to each infinite place $w$ a representation $\tau_w$ of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$ on a finite-dimensional complex space, each irreducible. Let the carrier pins be the production pins over $D$ with level map $N\mapsto \mathrm{principalLevel}(N)\cap\mathrm{GL}_2(\mathbb{A}_F)_{\mathrm f}$, Hecke generators $\mathrm{heckeGen}$ at the finite places, and the adelic box, and let $V$ be a cuspidal constituent for these pins and $\xi$: a nonzero submodule of $K$-finite cusp functions stable under right translation by finite-adelic elements and by row isometries at the infinite places and under right convolution by factorizable archimedeanly bi-finite test functions, minimal among such submodules inside it. Let $f$ be a factorizable test function (a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor) that is level-spherical of the type family with the single type $\tau_w$ at each $w$ and level $\mathrm{principalLevel}(N)\cap\mathrm{GL}_2(\mathbb{A}_F)_{\mathrm f}$, and assume $f$ is flat-symmetric, $\overline{f(y^{-1})}\,\|\det y\|^{-\sigma}=f(y)$ for all $y$. Then there is a real number $\lambda$ such that every $\varphi$ lying in $V$, invariant on the right under the level subgroup, and lying in the archimedean cut $\bigsqcap_w$ of the $\tau_w$-isotypic submodules satisfies $\varphi * f = \lambda\varphi$, where $(\varphi*f)(g)=\int \varphi(gx)f(x)\,d\mu(x)$ against the Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the scalar step of Schur's lemma for the smoothing (convolution) operators on a cuspidal constituent: the operator attached to a self-flat level-spherical test function of one irreducible archimedean type per place acts on the level-invariant, type-cut part of the constituent by a single real eigenvalue, the reality coming from the symmetry of the operator on the $L^2$ carrier. It is the principal-level form of the statement, and is used in establishing finite-dimensionality of the isotypic cusp spaces at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType_principal.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_ArchSpherical
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum

theorem AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType_principal
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hfT : IsFactorizableTestFn F f)
    (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)
        ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N) f)
    (hflat : flat F σ f = f) :
    ∃ lam : ℝ,
      ∀ φ ∈
        V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F),
        rightConv F φ f = (lam : ℂ) • φ := by sorry
