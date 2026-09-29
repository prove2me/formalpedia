-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_rightConv_ne_zero_of_ne_bot_principal
-- name    : AutomorphicForm.CuspidalSpectrum.exists_rightConv_ne_zero_of_ne_bot_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/cbd48dfe-f4c2-56b1-8c19-9d6fe9d273c3
-- title:
--   Flat level-spherical smoothing non-vanishing on a type cut
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals, let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$, let $\xi$ be a homomorphism from the full subgroup of ideles $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$ and $\sigma$ a real with $\|\xi(z)\| = \mathrm{ideleNorm}(z)^{\sigma}$ for all $z$, let $N$ be a non-zero ideal of $\mathcal{O}_F$, and for each infinite place $w$ let $\tau_w$ be a representation of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$ on $\mathbb{C}^{n_w}$, assumed irreducible. Write $\mathrm{pins}$ for the production carrier data attached to the window $D=\bigcup_{x\in T}\,\mathfrak{S}x$, where $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` (finite part integral, local height $\ge c$, $x$-window $\le u^2$, archimedean determinant norm in $[d_1,d_2]$ at every infinite place), with central subgroup $\top$, level map $N\mapsto U(N):=K(N)\cap\ker(\mathrm{glArch})$ given by the principal level subgroups, Hecke generators $\mathrm{heckeGen}$, and the measure on $\mathbb{A}_F$ conditioned on `adelicBox F`; the measure on $\mathrm{GL}_2(\mathbb{A}_F)$ is the Haar measure for the Borel structure. Let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a cuspidal constituent for $(\mathrm{pins},\xi)$: $V$ lies in the $K$-finite cusp submodule, is stable under right translation by elements of $\ker(\mathrm{glArch})$ and by the row isometries at each infinite place, is stable under right convolution by factorizable arch-bi-finite test functions, is non-zero, and is minimal among non-zero such submodules. Let $\mathrm{tys}$ be the type family with one constituent $\tau_w$ at each infinite place, and put $X = V \sqcap \{\varphi : \varphi(gu)=\varphi(g)\ \forall u\in U(N)\} \sqcap \bigsqcap_w (\text{the }\tau_w\text{-type submodule})$. Assume $X \ne 0$. Then there is $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a factorizable test function, admits an archimedean factor $f_a$ that is a smooth compactly supported function of the archimedean matrix entries, is arch-factor-bi-finite for $\mathrm{tys}$, satisfies $f_a(\iota_w(k)\,x\,\iota_w(k)^{-1}) = f_a(x)$ for every infinite place $w$, every row isometry $k$ at $w$ and every $x$, and such that $f(g) = f_a(g_\infty)\cdot \mathbf{1}_{\mathrm{glFin}(U(N))}(g_{\mathrm{fin}})$ for all $g$; moreover $f$ is flat-symmetric, $\overline{f(y^{-1})}\,\mathrm{ideleNorm}(\det y)^{-\sigma} = f(y)$, right convolution with $f$ maps $X$ into $X$, and there is $\varphi\in X$ with $\varphi * f \ne 0$, where $(\varphi * f)(g)=\int \varphi(gx)f(x)\,dx$.
--
--   This is the smoothing (approximate identity) step for automorphic forms at full principal level: it produces a single bi-$K$-type-adapted, level-spherical, flat-symmetric test function whose right convolution preserves the chosen isotypic cut of a cuspidal constituent and does not annihilate it. It is used in the proof that such a cut is spanned by right convolutions acting as scalars, which in turn feeds the finite-dimensionality of the principal-level isotypic cusp spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_rightConv_ne_zero_of_ne_bot_principal.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_rightConv_ne_zero_of_ne_bot_principal
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hX : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) ≠ ⊥) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      (∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) fa ∧
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g)) ∧
      flat F σ f = f ∧
      (∀ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F), rightConv F φ f ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)) ∧
      ∃ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F), rightConv F φ f ≠ 0 := by sorry
