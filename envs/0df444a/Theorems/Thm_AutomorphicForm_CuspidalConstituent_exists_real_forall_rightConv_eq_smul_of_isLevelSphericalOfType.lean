-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType
-- name    : AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/af164b26-e922-57e5-95b9-a926b256fb31
-- title:
--   Level-spherical convolution acts by a real scalar on a cuspidal constituent
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$ and $0<d_1<d_2$, and let $T$ be a finite set of points of $\mathrm{GL}_2$ of the adeles of $F$ such that the union $D=\bigcup_{x\in T}(\,\cdot\,x)$-translates of the centre-cut Siegel set with parameters $c,u,d_1,d_2$ (the $g$ whose finite part is integral, whose local heights at every infinite place are $\ge c$, whose window coordinates satisfy $\mathrm{xWindowSq}\le u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$) covers modulo centre: every adelic $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g z\in D$. Let $\xi$ be a character of the full idele unit group with $\|\xi(z)\|=\|z\|^{\sigma}$ for some real $\sigma$, let $N\neq 0$ be an ideal of $\mathcal O_F$, and let $\tau$ assign to each infinite place $w$ an archimedean datum $(n,\rho)$ with $\rho$ an irreducible representation of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$. Fix the pins `productionPinsOf` at $D$, with levels $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators `heckeGen` at the finite places, adelic Haar measure, full centre $Z=\top$, and the measure on the adeles conditioned on the adelic box. Let $V$ be a cuspidal constituent for $\xi$ at these pins: a $K$-finite cuspidal subspace stable under right translation by finite-adelic elements, by the archimedean row isometries, and under right convolution with arch-bi-finite factorisable test functions, nonzero, and minimal among such subspaces. Let $f$ be a factorisable test function (a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor) which is level-spherical of the one-dimensional arch type family $w\mapsto\tau w$ at level $U(N)$ — so $f(g)=f_\infty(g_\infty)\cdot\mathbf 1_{U(N)}(g_{\mathrm{fin}})$ with $f_\infty$ an arch test factor, bi-finite for that family and invariant under conjugation by each local row-isometry subgroup — and assume $f$ is fixed by the $\sigma$-weighted flat involution, $f(y)=\overline{f(y^{-1})}\,\|\det y\|^{-\sigma}$. Then there is a real number $\lambda$ such that $\varphi * f=\lambda\varphi$, the convolution being $g\mapsto\int\varphi(gx)f(x)\,dx$ against adelic Haar measure, for every $\varphi$ lying in $V$, invariant on the right under $U(N)$, and belonging to the archimedean cut $\bigcap_w$ of the $\tau w$-type submodules. The scalar is asserted only to exist; it may be zero, and the intersection may be the zero space.
--
--   This is the scalar step of Schur's lemma for the commuting family of level-spherical convolution operators of a single archimedean type acting on a cuspidal constituent at a fixed window of pins, the reality of the eigenvalue coming from self-adjointness under the flat involution. It feeds the finite-dimensionality and joint-eigenvector statements for cuspidal constituents, namely [`AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos`](thm.html#AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos) and [`AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent`](thm.html#AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum

theorem AutomorphicForm.CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hfT : IsFactorizableTestFn F f)
    (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)
        ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N) f)
    (hflat : flat F σ f = f) :
    ∃ lam : ℝ,
      ∀ φ ∈
        V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F),
        rightConv F φ f = (lam : ℂ) • φ := by sorry
