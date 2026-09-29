-- Prove2me | Theorems.Thm_AutomorphicForm_exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule
-- name    : AutomorphicForm.exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/48dc866c-5a9d-5161-9120-8d5e90f29780
-- title:
--   Reproduction and Whittaker properties of isotypic cusp forms over ℚ
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T\subset \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, and let $D=\bigcup_{x\in T}\{g x\}$ be the union of the right translates by $T$ of the centre-cut Siegel set $\{g:\ \text{the finite part of }g\text{ is integral},\ \mathrm{localHeight}\ge c\text{ and } \mathrm{xWindowSq}\le u^2\text{ at every infinite place},\ \text{all archimedean determinant norms in }[d_1,d_2]\}$; assume $D$ covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and a central idele scalar $z$ with $\gamma g z\in D$. Work at the pins `productionPinsOf` with carrier $D$, level groups $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}(v)$, central subgroup $\top$, Haar measure on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, and additive measure the adelic Haar measure conditioned on the adelic box. Let $\Phi$ be a complex Hecke eigensystem, $\xi$ a character of the central subgroup, $S$ a finite set of primes of $\mathbb{Z}$, and let $\varphi\ne 0$ satisfy `IsIsotypicCuspFormAt`: it is continuous, a smooth cuspidal automorphic function with central datum $\xi$, right invariant under $U(\mathrm{level}\,\Phi)$, a Hecke coset eigenfunction with eigenvalue $\Phi.a(v)$ for $v\notin S$, and satisfies $\varphi(\mathrm{centralScalar}(\det \mathrm{heckeGen}(v))g)=\mathrm{cNorm}(v)^{-1}\Phi.b(v)\varphi(g)$ for $v\notin S$. Assume finally, for every infinite place $w$, a homomorphism $\chi_w$ from `rowIsometrySubgroup₀` of $w$'s completion to $\mathbb{C}^\times$ together with `HasArchCharacterAt₀ ℚ w (χ w) φ`, the condition that $\varphi$ has archimedean type $\chi_w$ at $w$. Then four assertions hold. First, there is a factorizable test function $\gamma$ (a product of a compactly supported archimedean factor smooth in the matrix entries with a locally constant compactly supported finite factor) whose support consists of products $a k$ with $a$ of trivial finite part and $k\in \mathrm{levelOne}(\mathrm{level}\,\Phi)\cap\ker(\mathrm{glArch})$, and which reproduces $\varphi$: $\int \varphi(gx)\gamma(x)\,dx=\varphi(g)$. Second, for every real infinite place $w$, all $c_H,c_E,c_F,c_0\in\mathbb{C}$ and every $t$ with trivial finite part, the function $\varphi+c_0\bigl(g\mapsto (c_H D_H\varphi+c_E D_E\varphi+c_F D_{F^-}\varphi)(gt)\bigr)$ is again an isotypic cusp form for the same data, where $D_d\varphi(g)$ is the derivative at $0$ of $t\mapsto\varphi(g\,\mathrm{archFlowAt}(w,d,t))$. Third, for every continuous nontrivial additive character $\psi$ of $\mathbb{A}_\mathbb{Q}$ trivial on $\mathbb{Q}$ and every real place $w$ at which $\varphi$ is archimedean-smooth, all Whittaker integrands for $\varphi$ and for each $D_d\varphi$ (all $\alpha\in\mathbb{Q}$, all $g$) are integrable, and there is a $g$ with the $\alpha=1$ Whittaker coefficient of $\varphi$ nonzero. Fourth, for every such $\psi$ and every $t$ of trivial archimedean part there are constants $C,M$ with $\bigl\|W_\psi(\varphi,1)(\mathrm{diagOne}(a)\,t)\bigr\|\le C\,\|a\|^{M}$ for all ideles $a$ with trivial finite component, $\|a\|$ the idele norm.
--
--   This packages the standard analytic facts about a $K$-finite isotypic cuspidal automorphic function on $\mathrm{GL}_2$ over $\mathbb{Q}$: exact reproduction by a single factorizable test function, stability of the isotypic cusp form condition under the three archimedean flow derivations, and integrability, non-vanishing and polynomial torus growth of its Whittaker coefficients. It feeds the converse-theorem input of the Langlands–Tunnell step, being used in the construction of a Whittaker factorization for weight-one Casimir eigenvectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem AutomorphicForm.exists_rightConv_eq_self_and_isIsotypicCuspFormAt_add_smul_archDerivAt_and_whittakerCoefficient_bounds_of_mem_archCutSubmodule
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (ξ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ Φ.level S Φ φ)
    (hne : φ ≠ 0)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (harch : ∀ w : InfinitePlace ℚ, HasArchCharacterAt₀ ℚ w (χ w) φ) :

    (∃ γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ γ ∧
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, γ x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
        glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) ∧
      rightConv ℚ φ γ = φ) ∧

    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (cH cE cF c₀ : ℂ) (t : AdelicGL2 (𝓞 ℚ) ℚ), glFin (𝓞 ℚ) ℚ t = 1 →
      IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ξ Φ.level S Φ
        (φ + c₀ • fun g =>
          (cH • archDerivAt hw ArchDir.H φ + cE • archDerivAt hw ArchDir.E φ + cF • archDerivAt hw ArchDir.Fm φ)
            (g * t))) ∧

    (∀ ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ, IsGlobalAddChar ℚ ψ → ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ →
        (∀ (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), WhittakerCoefficientIntegrable ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ φ α g) ∧
        (∀ (d : ArchDir) (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), WhittakerCoefficientIntegrable ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ (archDerivAt hw d φ) α g) ∧
        ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, whittakerCoefficient ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          ψ φ 1 g ≠ 0) ∧

    (∀ ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ, IsGlobalAddChar ℚ ψ →
      ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, t ∈ finiteAdelicGL2Subgroup ℚ →
        ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
          ‖whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
                (adelicBox ℚ)) ψ φ 1 (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M) := by sorry
