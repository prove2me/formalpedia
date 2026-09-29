-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
-- name    : AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/2d75a8a5-e6e4-5d9c-8efd-9bb025084651
-- title:
--   Parseval identity for pseudo-Eisenstein series with residual term
-- statement:
--   Let $F$ be a number field, write $\mathbb{A}=\mathbb{A}_F$ for its adele ring and $G=\mathrm{GL}_2(\mathbb{A})$ for `AdelicGL2 (𝓞 F) F`. Put $\alpha$ for the monoid homomorphism from $\mathbb{A}^\times$ to $\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}$ followed by the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$, passed to units, and assume `hα`, that $\alpha(x)>0$ for all $x$.
--
--   *Slab and fundamental domain.* Reals $d_1<d_2$ with $0<d_1$ are given, together with a set $\Phi\subseteq G$ contained in the determinant slab $\{g : \|\det g\|\in[d_1,d_2]\}$ (the idele norm being [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)), and the hypothesis `_hΦ` that $\Phi$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ under `globalPoints` acting on the slab, for the Haar measure `adelicGLHaar` restricted to that slab.
--
--   *Two measure-theoretic normalisations.* A constant $c\in[0,\infty]$, neither $0$ nor $\infty$, is given with the Iwasawa-type integration formula `_hc`: for every measurable $H:G\to[0,\infty]$, the Haar integral of $H$ equals $c$ times the iterated integral, over $x\in\mathbb{A}$, $u$ and $t$ in $\mathbb{A}^\times$ and $k$ in the maximal compact subgroup `adelicMaximalCompact F` with measure `maximalCompactHaar`, of $H\bigl(n(x)\,z(u)\,\mathrm{diag}(t,1)\,k\bigr)\cdot\|t\|^{-1}$, where $n(x)$ is the upper unipotent matrix and $z(u)$ the central scalar. A measurable set $D\subseteq\mathbb{A}^\times$ is given which is a fundamental domain for the subgroup of principal ideles with respect to `idelicHaar`, and a constant $V\ne 0,\infty$ with `_hV`: for every measurable $f:\mathbb{R}\to[0,\infty]$, $\int_D f(\|z\|)\,dz = V\int_{(0,\infty)} f(y)\,y^{-1}\,dy$.
--
--   *Carrier and central character.* All automorphic data are taken with respect to the carrier pins `productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)`, whose measurable space and measure are the Borel structure and Haar measure on $G$, whose region is $\Phi$, whose subgroup $Z$ is the whole group $\mathbb{A}^\times$, and whose adelic measure is `adelicAddHaar` conditioned on `adelicBox F`. Thus $\xi$ is a character $Z\to\mathbb{C}^\times$ of the full idele group.
--
--   *Character data.* A finite index type $\iota$ is given together with families $\mu,\nu:\iota\to\mathrm{Hom}(\mathbb{A}^\times,\mathbb{C}^\times)$ subject to: `_hμ`, `_hν`, each $\mu_e$ and $\nu_e$ is unitary, $|\chi(x)|=1$ for all $x$; `_hμic`, `_hνic`, each is trivial on principal ideles; `_hμc`, `_hνc`, each $\mu_e$ and $\nu_e$ is continuous; `_hμν`, $\mu_e(z)\nu_e(z)=\xi(z)$ for all $e$ and all $z\in Z$; a map $r:\iota\to\iota$ with `_hr`, $\mu_{r e}=\nu_e$ and $\nu_{r e}=\mu_e$; and `_hdist`, for $e\ne e'$ there is a norm-one idele $x$ with $\mu_e(x)\ne\mu_{e'}(x)$ or $\nu_e(x)\ne\nu_{e'}(x)$.
--
--   *Families of sections.* Families $\varphi_f,\psi_f:\iota\to\mathbb{C}\to G\to\mathbb{C}$ are given with: `_hφf`, `_hψf`, for all $e$ and $s$ both $\varphi_f(e,s)$ and $\psi_f(e,s)$ are induced sections for the pair of characters $\eta_1=\mu_e\cdot\alpha^{\,s+1/2}$ and $\eta_2=\nu_e\cdot\alpha^{-(s+1/2)}$, that is, $\phi(bg)=\eta_1(b_{11})\eta_2(b_{22})\phi(g)$ for every $b$ in the adelic Borel subgroup (lower-left entry zero) and every $g$; `_hφjc`, `_hψjc`, joint continuity in $(s,g)$; `_hφhol`, `_hψhol`, holomorphy in $s$ for each fixed $g$; `_hψK`, each $\psi_f(e,s)$ is archimedean $K$-finite (finitely many spanning right translates under each `archRowIsometrySubgroup F w`); `_hψsm`, each $\psi_f(e,s)$ is $K_f$-smooth, the stabiliser in the finite adelic subgroup of the right-translation function being open; `_hψKu`, for each $e$ and each infinite place $w$ a single finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup F w` containing $k\mapsto\psi_f(e,s)(gk)$ for all $s$ and $g$; and `_hφdec`, `_hψdec`, rapid decay on vertical lines uniformly on compacta: for each $e$, each $n\in\mathbb{N}$, each $\sigma_0$ and each compact $C\subseteq G$ there is an integrable, bounded $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\,\|\phi(\sigma'+it)(g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$.
--
--   *Profiles and their contour representations.* Functions $\varphi,\psi:G\to\mathbb{C}$ are given which are slab profiles for $(Z,\xi)$ in the sense of `IsSlabProfile`: measurable, invariant under left multiplication by unipotent $n(x)$, $x\in\mathbb{A}$, invariant under left multiplication by the global points of the Borel subgroup, transforming by $\xi(z)$ under left multiplication by central scalars $z\in Z$, bounded on every slab $\|\det g\|\in[d_1,d_2]$ with $d_1>0$, and with support contained in a band $a\le\mathrm{ht}(g)\le b$, $a>0$, for the adelic height. The hypotheses `_hφrep`, `_hψrep` state that for every real $\sigma'$ and every $g$, $\varphi(g)=\sum_e (4\pi)^{-1}\int_{\mathbb{R}}\varphi_f(e,\sigma'+it)(g)\,dt$, and likewise for $\psi$ with $\psi_f$.
--
--   *Intertwining continuation.* A family $Mc:\iota\to\mathbb{C}\to G\to\mathbb{C}$ is given with `_hMc`: for each $e$ and each $g$, the function $s\mapsto Mc(e,s)(g)$ is meromorphic in normal form on all of $\mathbb{C}$, and for $\mathrm{Re}\,s>1/2$ it equals the Weyl intertwining integral $\int_{\mathbb{A}}\psi_f(e,s)(w^{-1}n(x)g)\,dx$ taken against `adelicAddHaar`, $w$ being the global Weyl element.
--
--   *Residual projections.* Functions $p_\varphi,p_\psi:G\to\mathbb{C}$ are given which are automorphic at the carrier with character $\xi$ (`IsAutomorphicFnAt`), together with: `_hpφc`, `_hpψc`, for every $\varepsilon>0$ there is an element $q$ of the residual span — the $\mathbb{C}$-span of the functions $g\mapsto\chi(\det g)$ for characters $\chi$ of $\mathbb{A}^\times$ with $\chi^2=\xi$ on $Z$ — which is automorphic at the carrier and satisfies $\|p_\varphi-q\|_{L^2(\Phi)}<\varepsilon$, respectively $\|p_\psi-q\|_{L^2(\Phi)}<\varepsilon$; and `_hpφo`, `_hpψo`, orthogonality on $\Phi$: for every $h$ which is automorphic at the carrier and lies in the residual span, $\int_\Phi\bigl(\theta_\varphi(g)-p_\varphi(g)\bigr)\overline{h(g)}\,dg=0$ and $\int_\Phi\bigl(\theta_\psi(g)-p_\psi(g)\bigr)\overline{h(g)}\,dg=0$, where $\theta_\phi=$ `pseudoEisenstein F` $\phi$ is the function $g\mapsto \phi(g)+\sum_{\beta\in F}^{\prime}\phi\bigl(w\,n(\beta)\,g\bigr)$.
--
--   *Conclusion.* Under these hypotheses,
--   $$\int_\Phi \theta_\varphi(g)\,\overline{\theta_\psi(g)}\,dg \;=\; \int_\Phi p_\varphi(g)\,\overline{p_\psi(g)}\,dg \;+\; \kappa\sum_{e\in\iota}\int_{\mathbb{R}}\Bigl(A_e(t)+\mathrm{vol}(B)^{-1}B_e(t)\Bigr)dt,$$
--   both integrals over $\Phi$ being taken against the Haar measure of the carrier, where $\mathrm{vol}(B)$ is the real number `(adelicAddHaar (𝓞 F) F) (adelicBox F)` in $[0,\infty]$ converted to $\mathbb{R}$, the scalar is the complex number
--   $$\kappa=\frac{c\cdot \mathrm{vol}(B)\cdot V^2\cdot \log(d_2/d_1)}{16\pi}$$
--   with $c$ and $V$ likewise converted to real numbers, and, for each $e$ and each real $t$,
--   $$A_e(t)=\int_K \varphi_f(e,it)(k)\,\overline{\psi_f(e,it)(k)}\,dk,\qquad B_e(t)=\int_K \varphi_f(e,it)(k)\,\overline{\lim_{s\to -it,\ s\ne -it} Mc(r e,s)(k)}\,dk,$$
--   the integrals over the maximal compact subgroup being taken against `maximalCompactHaar F`, and the inner limit being `Filter.limUnder` along the punctured neighbourhood filter of $-it$ of the function $s\mapsto Mc(r e,s)(k)$.
--
--   This is the Parseval (inner product) identity for pseudo-Eisenstein series on $\mathrm{GL}_2$ over a number field, restricted to a determinant slab: the $L^2$ pairing of two pseudo-Eisenstein series splits into the pairing of their residual projections and a contour integral along the unitary axis of the pairings of the defining sections with each other and with the analytic continuation of the Weyl intertwining operator. It is used in the subsequent norm and convolution identities for pseudo-Eisenstein series at principal level, and in the orthogonality statement against cusp-form bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
            (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (c : ℝ≥0∞) (_hc0 : c ≠ 0) (_hcT : c ≠ ∞)
      (_hc : ∀ H : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable H →
        ∫⁻ g, H g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                H (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
      (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
      (ι : Type) [Fintype ι]
      (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 F) F (ν e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ι)
        (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)
      (r : ι → ι) (_hr : ∀ e, μ (r e) = ν e ∧ ν (r e) = μ e)
      (_hdist : ∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)
      (φf ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite F (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth F (ψf e s))
      (_hψKu : ∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (φ ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
      (_hψ : AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ)
      (_hφrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (Mc : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ (e : ι) (g : AdelicGL2 (𝓞 F) F), MeromorphicNFOn (fun s : ℂ => Mc e s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc e s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e s) g)
      (pφ pψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hpφ : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ pφ)
      (_hpψ : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ pψ)
      (_hpφc : ∀ ε > (0:ℝ),
        ∃ q ∈ AutomorphicForm.residualSpan (𝓞 F) F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).Z ξ,
          IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ q ∧
          eLpNorm (pφ - q) 2
            ((productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).μ.restrict
              (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).D) < ENNReal.ofReal ε)
      (_hpψc : ∀ ε > (0:ℝ),
        ∃ q ∈ AutomorphicForm.residualSpan (𝓞 F) F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).Z ξ,
          IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ q ∧
          eLpNorm (pψ - q) 2
            ((productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).μ.restrict
              (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).D) < ENNReal.ofReal ε)
      (_hpφo : ∀ h : AdelicGL2 (𝓞 F) F → ℂ,
        IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ h →
        h ∈ AutomorphicForm.residualSpan (𝓞 F) F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).Z ξ →
          ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).D,
              (AutomorphicForm.pseudoEisenstein F φ g - pφ g) * starRingEnd ℂ (h g)
            ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).μ = 0)
      (_hpψo : ∀ h : AdelicGL2 (𝓞 F) F → ℂ,
        IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ h →
        h ∈ AutomorphicForm.residualSpan (𝓞 F) F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).Z ξ →
          ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).D,
              (AutomorphicForm.pseudoEisenstein F ψ g - pψ g) * starRingEnd ℂ (h g)
            ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).μ = 0),
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
        AutomorphicForm.pseudoEisenstein F φ g * starRingEnd ℂ (AutomorphicForm.pseudoEisenstein F ψ g)
      ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ =
    (∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
        pφ g * starRingEnd ℂ (pψ g)
      ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ) +
    ((c.toReal * ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal * V.toReal ^ 2
        * Real.log (d₂ / d₁) / (16 * Real.pi) : ℝ) : ℂ) *
    ∑ e, ∫ t : ℝ,
      ((∫ k, φf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
            * starRingEnd ℂ (ψf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
          ∂(maximalCompactHaar F))
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          ∫ k, φf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
            * starRingEnd ℂ (Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I)))
                (fun s : ℂ => Mc (r e) s (k : AdelicGL2 (𝓞 F) F)))
          ∂(maximalCompactHaar F)) := by sorry
