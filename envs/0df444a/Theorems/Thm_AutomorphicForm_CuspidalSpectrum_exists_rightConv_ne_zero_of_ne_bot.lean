-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_rightConv_ne_zero_of_ne_bot
-- name    : AutomorphicForm.CuspidalSpectrum.exists_rightConv_ne_zero_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/e42a8577-9d34-5499-b59a-c1be44280c09
-- title:
--   Flat-symmetric smoothing non-zero on a cuspidal type cut
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers and $T$ a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and put $D=\bigcup_{x\in T}\{g x : g\in \Sigma\}$, where $\Sigma$ is the set of $g$ whose finite part is integral, with $\mathrm{localHeight}\ge c$, $\mathrm{xWindowSq}\le u^2$ and archimedean determinant norm in $[d_1,d_2]$ at every infinite place. Let `pins` be `productionPinsOf` applied to $D$, to the level subgroups $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, to the local Hecke generators $\mathrm{heckeGen}$ and to the adelic box (so the measures are Borel Haar on $\mathrm{GL}_2(\mathbb{A}_F)$ and additive Haar conditioned on the box, and the centre subgroup is all of $\mathbb{A}_F^\times$). Let $\xi:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be a character with $\|\xi(z)\|=\|z\|^{\sigma}$ for a real $\sigma$, let $N\neq 0$ be an ideal of $\mathcal{O}_F$, and for each infinite place $w$ let $\tau_w$ be a representation of $\mathrm{rowIsometrySubgroup}_0(F_w)$ on some $\mathbb{C}^{n_w}$, assumed irreducible. Let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a cuspidal constituent for `pins` and $\xi$, i.e. $V$ is a non-zero cusp subrepresentation (contained in `cuspKFiniteSubmodule`, stable under right translation by the finite subgroup and by the archimedean row-isometry subgroups, and stable under right convolution by factorizable bi-finite test functions) all of whose cusp subrepresentations are $0$ or $V$. Write $X=V\cap L\cap A$, where $L$ consists of the $\varphi$ with $\varphi(gu)=\varphi(g)$ for all $u\in U(N)$ and $A$ is the type cut `archCutSubmodule` for the family assigning the single type $\tau_w$ to each $w$, and assume $X\neq 0$. Then there is $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that: $f$ is factorizable as a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor; there is an archimedean factor $f_a$ that is smooth and compactly supported in the matrix entries, satisfies `IsArchFactorBiFinite` for the above type family, is invariant under conjugation by $\mathrm{archRowIsometryInclAt}_0(w,k)$ for every infinite place $w$ and every $k$, and satisfies $f(g)=f_a(\mathrm{glArch}\,g)\cdot\mathbf 1_{\mathrm{glFin}(U(N))}(\mathrm{glFin}\,g)$; $f$ is flat-symmetric, $f(y)=\overline{f(y^{-1})}\,\|\det y\|^{-\sigma}$; right convolution $\varphi\mapsto\int \varphi(g x)f(x)\,dx$ maps $X$ into $X$; and $\mathrm{rightConv}\,\varphi\,f\neq 0$ for some $\varphi\in X$.
--
--   This is the non-vanishing input for the admissibility and eigenvalue-capture argument for cuspidal constituents of $\mathrm{GL}_2$ over a number field: it provides a level-spherical, flat-symmetric smoothing operator that preserves the single-type, level-$N$ cut of a cuspidal constituent and does not annihilate it. It is used in the dichotomy statement [`AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent`](thm.html#AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_rightConv_ne_zero_of_ne_bot.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_rightConv_ne_zero_of_ne_bot
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hX : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) ≠ ⊥) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      (∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) fa ∧
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g)) ∧
      flat F σ f = f ∧
      (∀ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F), rightConv F φ f ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)) ∧
      ∃ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F), rightConv F φ f ≠ 0 := by sorry
