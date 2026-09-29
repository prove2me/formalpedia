-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_normSq_add_weylIntertwining_of_principalLevel_slab
-- name    : AutomorphicForm.setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_normSq_add_weylIntertwining_of_principalLevel_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/bf1d43ae-33bc-5e08-afe5-45c2874f493b
-- title:
--   Plancherel identity for the continuous part of a pseudo-Eisenstein series
-- statement:
--   Let $F$ be a number field, and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the idele norm regarded as a homomorphism into the units of $\mathbb{R}$, that is, the distributive Haar character `distribHaarChar (AdeleRing (𝓞 F) F)` of the adele ring pushed into $\mathbb{R}$ and viewed as a map to units; the hypothesis `hα` records that $\alpha(x)$ is positive for every $x$.
--
--   The geometric data are: reals $d_1 < d_2$ with $0 < d_1$; a set $\Phi \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ contained in the determinant slab $\{g : \|\det g\| \in [d_1,d_2]\}$ (the norm being [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)), which is a fundamental domain for the action of the image of $\mathrm{GL}_2(F)$ under `globalPoints` on that slab, for the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F` restricted to the slab. Throughout, the remaining data on $\mathrm{GL}_2$ are those packaged by `productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)`: the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the domain $\Phi$, the full idele group $\top$ as central group, the level subgroups $N \mapsto$ `levelOne (𝓞 F) F N`, the Hecke elements $v \mapsto$ `heckeGen (𝓞 F) F v`, and the additive adelic Haar measure conditioned on the box `adelicBox F`.
--
--   Three measure normalisations are assumed. A constant $c \in [0,\infty]$, neither $0$ nor $\infty$, gives an Iwasawa disintegration: for every measurable $H : \mathrm{GL}_2(\mathbb{A}_F) \to [0,\infty]$, the integral of $H$ against `adelicGLHaar` equals $c$ times the iterated integral, over $x$ in the adeles (additive Haar), over $u$ and $t$ in the ideles (idelic Haar) and over $k$ in `adelicMaximalCompact F` (the group of elements integral at all finite places and row-isometric at all infinite places, with its Haar measure `maximalCompactHaar F`), of $H\bigl(n(x)\, z(u)\, \mathrm{diag}(t,1)\, k\bigr)\,\|t\|^{-1}$, where $n(x) =$ `unipotentGL2 x`, $z(u)$ is the central scalar and $\mathrm{diag}(t,1) =$ `diagOne t`. A measurable set $D \subseteq (\mathbb{A}_F)^\times$ is a fundamental domain for the subgroup of principal ideles [`M4aHerbrand.principalIdeles (𝓞 F) F`](def/M4aHerbrand_IdeleClassVocab.html#L16) acting on the ideles with idelic Haar measure. A constant $V$, neither $0$ nor $\infty$, gives the Mellin normalisation: for every measurable $f : \mathbb{R} \to [0,\infty]$, $\int_D f(\|z\|)\,dz = V \int_{(0,\infty)} f(y)\,y^{-1}\,dy$.
--
--   Let $\xi$ be a homomorphism from the central group $\top$, i.e. from $(\mathbb{A}_F)^\times$, to $\mathbb{C}^\times$. Let $\iota$ be a finite index type and $\mu, \nu : \iota \to ((\mathbb{A}_F)^\times \to \mathbb{C}^\times)$ two families of characters subject to: unitarity of every $\mu_e$ and every $\nu_e$ (`IsUnitaryChar`: all values of absolute value $1$); triviality on principal ideles (`IsIdeleClassChar`); continuity of $x \mapsto \mu_e(x)$ and of $x \mapsto \nu_e(x)$; the product relation $\mu_e(z)\nu_e(z) = \xi(z)$ for all $e$ and all $z$ in the central group; a swap $r : \iota \to \iota$ with $\mu_{r e} = \nu_e$ and $\nu_{r e} = \mu_e$ for every $e$; and separation, namely for $e \neq e'$ there is an $x$ in [`NumberField.TateGlobal.normOneIdeles F`](def/NumberField_TateGlobalZeta.html#L16) with $\mu_e(x) \neq \mu_{e'}(x)$ or $\nu_e(x) \neq \nu_{e'}(x)$.
--
--   Let $\psi f : \iota \to \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family of sections. The hypotheses on it are: for each $e$ and $s$, $\psi f_e(s)$ is an induced section for the pair `etaFst (μ e) α hα s` $= \mu_e \cdot \alpha^{s+1/2}$ and `etaSnd (ν e) α hα s` $= \nu_e \cdot \alpha^{-(s+1/2)}$, that is, $\psi f_e(s)(bg)$ equals the first character at the $(0,0)$ entry of $b$ times the second character at the $(1,1)$ entry of $b$ times $\psi f_e(s)(g)$, for all $b$ in the adelic Borel subgroup (entry $(1,0)$ zero) and all $g$; joint continuity of $(s,g) \mapsto \psi f_e(s)(g)$; holomorphy of $s \mapsto \psi f_e(s)(g)$ for each $g$; archimedean $K$-finiteness `IsArchKFinite` and $K_f$-smoothness `IsKfSmooth` (openness of the stabiliser inside the kernel `finiteAdelicGL2Subgroup F` of the archimedean projection) of each $\psi f_e(s)$; uniformity of the archimedean type, namely for each $e$ and each infinite place $w$ a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup F w` containing every right-translate function $k \mapsto \psi f_e(s)(gk)$, for all $s$ and $g$; invariance under a fixed level, namely a nonzero ideal $N$ of $\mathcal{O}_F$ with $\psi f_e(s)(gu) = \psi f_e(s)(g)$ for all $u$ in `principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`; and rapid decay on vertical strips, namely for each $e$, each $n \in \mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded-above $m : \mathbb{R} \to \mathbb{R}$ with $(1+|t|)^n \,\|\psi f_e(\sigma' + it)(g)\| \le m(t)$ for all $|\sigma'| \le \sigma_0$, all $t$ and all $g \in C$.
--
--   Let $\psi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfy `IsSlabProfile F ⊤ ξ ψ`: $\psi$ is measurable, left invariant under all unipotents $n(x)$ with $x$ adelic and under left translation by the global points of the Borel subgroup of $\mathrm{GL}_2(F)$, transforms by $\xi$ under left translation by central scalars from the central group, is bounded on every determinant slab $[d_1', d_2']$ with $d_1' > 0$, and is supported where the adelic height [`NumberField.AdelicHeight.adelicHeight F`](def/NumberField_AdelicHeight.html#L158) lies in some band $[a,b]$ with $a > 0$. Moreover $\psi$ is represented by the contour integrals of the family, uniformly in the abscissa: for every real $\sigma'$ and every $g$, $\psi(g) = \sum_{e} (4\pi)^{-1} \int_{\mathbb{R}} \psi f_e(\sigma' + it)(g)\,dt$.
--
--   Let $Mc : \iota \to \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be such that for each $e$ and $g$ the function $s \mapsto Mc_e(s)(g)$ is meromorphic in normal form on all of $\mathbb{C}$ and agrees, for $\operatorname{Re} s > 1/2$, with the Weyl intertwining integral `weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e s)` at $g$, i.e. with $\int_{\mathbb{A}_F} \psi f_e(s)(w^{-1} n(x) g)\,dx$ for the adelic Weyl element $w$.
--
--   Finally, let $p\psi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a residual projection: $p\psi$ satisfies `IsAutomorphicFnAt` for the above data and $\xi$ (the predicate `LsXiMember` for the Haar measure, the domain $\Phi$, the central group and $\xi$); for every $\varepsilon > 0$ there is a $q$ in the residual span [`AutomorphicForm.residualSpan`](def/AutomorphicForm_ResidualSpan.html#L12) — the complex span of the functions $g \mapsto \chi(\det g)$ for characters $\chi$ with $\chi^2 = \xi$ on the central group — which itself satisfies `IsAutomorphicFnAt` and for which the $L^2$ norm of $p\psi - q$ over $\Phi$ is less than $\varepsilon$; and $\theta_\psi - p\psi$ is orthogonal to the residual span, in the sense that $\int_{\Phi} (\theta_\psi(g) - p\psi(g))\,\overline{h(g)}\,dg = 0$ for every $h$ which satisfies `IsAutomorphicFnAt` and lies in the residual span. Here $\theta_\psi =$ [`AutomorphicForm.pseudoEisenstein F ψ`](def/AutomorphicForm_SlabProfile.html#L32) is the pseudo-Eisenstein series $\theta_\psi(g) = \psi(g) + \sum_{\beta \in F}' \psi(w\, n(\beta)\, g)$.
--
--   The conclusion is the identity
--   $$\int_{\Phi} (\theta_\psi(g) - p\psi(g))\,\overline{(\theta_\psi(g) - p\psi(g))}\,dg = \frac{c\,\mathrm{vol}\,V^2\,\log(d_2/d_1)}{32\pi}\, \sum_{e \in \iota} \int_{\mathbb{R}} \int_{K} A_e(t,k)\,\overline{A_e(t,k)}\,dk\,dt,$$
--   where the left-hand integral is against the Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, $\mathrm{vol}$ denotes the real number `((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal`, the constants $c$ and $V$ enter through their real values, the inner integral is over $K =$ `adelicMaximalCompact F` against `maximalCompactHaar F`, and
--   $$A_e(t,k) = \psi f_e(it)(k) + \mathrm{vol}^{-1}\,\lim_{s \to -it,\ s \neq -it} Mc_{r e}(s)(k),$$
--   the limit being `Filter.limUnder` along the punctured neighbourhood filter of $-it$. The scalar factor is a real number cast into $\mathbb{C}$, and the conjugations are `starRingEnd ℂ`, so both sides are squared $L^2$ norms written as products with complex conjugates.
--
--   This is the Plancherel (inner product) identity of Langlands' spectral theory in the diagonal case: the squared $L^2$ norm over a slab fundamental domain of the non-residual part $\theta_\psi - p\psi$ of a Paley–Wiener pseudo-Eisenstein series equals an integral over the unitary axis of the $L^2(K)$ norms of the outgoing data $\psi f_e(it) + \mathrm{vol}^{-1} Mc_{r e}(-it)$. It is obtained as the $\varphi = \psi$ case of the Parseval identity with residual term [`AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab`](thm.html#AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab), together with the automorphy of the pseudo-Eisenstein series and the normal-form analysis of the intertwining integral on vertical lines, and it feeds the existence statement [`AutomorphicForm.exists_forall_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_sum_normSq_inner_axis_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_sum_normSq_inner_axis_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_normSq_add_weylIntertwining_of_principalLevel_slab.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
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

theorem AutomorphicForm.setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_normSq_add_weylIntertwining_of_principalLevel_slab
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
      (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite F (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth F (ψf e s))
      (_hψKu : ∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (N : Ideal (𝓞 F)) (_hN : N ≠ ⊥)
      (_hψlev : ∀ e (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ψf e s (g * u) = ψf e s g)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (Mc : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ (e : ι) (g : AdelicGL2 (𝓞 F) F), MeromorphicNFOn (fun s : ℂ => Mc e s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc e s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e s) g)
      (pψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hpψ : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ pψ)
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
        (AutomorphicForm.pseudoEisenstein F ψ g - pψ g) * starRingEnd ℂ (AutomorphicForm.pseudoEisenstein F ψ g - pψ g)
      ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ =
    ((c.toReal * ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal * V.toReal ^ 2
        * Real.log (d₂ / d₁) / (32 * Real.pi) : ℝ) : ℂ) *
    ∑ e, ∫ t : ℝ,
      ∫ k, (ψf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
              + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
                Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I)))
                  (fun s : ℂ => Mc (r e) s (k : AdelicGL2 (𝓞 F) F)))
          * starRingEnd ℂ
            (ψf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
              + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
                Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I)))
                  (fun s : ℂ => Mc (r e) s (k : AdelicGL2 (𝓞 F) F)))
        ∂(maximalCompactHaar F) := by sorry
