-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_residualProj_mul_conj_eq_sum_integral_maximalCompact_residue_pairing_slab
-- name    : AutomorphicForm.setIntegral_residualProj_mul_conj_eq_sum_integral_maximalCompact_residue_pairing_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/6cb09ab3-865a-5255-8083-3c4d4bd87b0a
-- title:
--   Residual pairing for pseudo-Eisenstein series over a determinant slab
-- statement:
--   Let $F$ be a number field and let $\alpha \colon (\mathbf{A}_F)^\times \to \mathbb{R}^\times$ be the homomorphism of unit groups obtained from the module character `distribHaarChar (AdeleRing (𝓞 F) F)` composed with the ring homomorphism $\mathbb{R}_{\ge 0} \to \mathbb{R}$; the hypothesis `hα` requires $\alpha$ to take strictly positive values (so that the complex powers $\alpha(\cdot)^s$ used below are defined).
--
--   The data are as follows.
--
--   *Slab and fundamental domain.* Reals $d_1 < d_2$ with $0 < d_1$, and a set $\Phi \subseteq \mathrm{GL}_2(\mathbf{A}_F)$ which (hypothesis `_hΦs`) is contained in the slab $\{g : \|\det g\| \in [d_1,d_2]\}$, where $\|\cdot\|$ is [`NumberField.TateGlobal.ideleNorm F`](def/NumberField_TateGlobalZeta.html#L19), and which (hypothesis `_hΦ`) is a fundamental domain for the image of $\mathrm{GL}_2(F)$ under `globalPoints` acting on the Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F` restricted to that slab.
--
--   *Iwasawa constant.* A constant $c \in [0,\infty]$, neither $0$ nor $\infty$, such that (hypothesis `_hc`) for every measurable $H \colon \mathrm{GL}_2(\mathbf{A}_F) \to [0,\infty]$ the Haar integral of $H$ equals $c$ times the iterated lower integral, over $x \in \mathbf{A}_F$ (additive Haar `adelicAddHaar`), then $u$ and $t$ in the idele group (measure [`NumberField.Idele.idelicHaar F`](def/NumberField_IdeleProductMeasure.html#L391) for each), then $k$ in the compact group `adelicMaximalCompact F` (measure `maximalCompactHaar F`), of
--   $$H\bigl(\mathrm{unipotentGL2}(x)\cdot \mathrm{centralScalar}(u)\cdot \mathrm{diagOne}(t)\cdot k\bigr)\,\cdot\, \|t\|^{-1},$$
--   where `unipotentGL2 x` is the upper unipotent matrix with entry $x$, `centralScalar u` the scalar matrix $u$, `diagOne t` the diagonal matrix $\mathrm{diag}(t,1)$, and `adelicMaximalCompact F` the subgroup of elements whose finite part is integral and whose component at each infinite place is a row isometry.
--
--   *Norm disintegration.* A measurable set $D$ of ideles which is a fundamental domain for the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) of principal ideles with respect to `idelicHaar F`, and a constant $V \in [0,\infty]$, neither $0$ nor $\infty$, such that (hypothesis `_hV`) for every measurable $f \colon \mathbb{R} \to [0,\infty]$ one has $\int^-_{D} f(\|z\|)\,dz = V \int^-_{(0,\infty)} f(y)\,y^{-1}\,dy$.
--
--   *Central character.* A homomorphism $\xi$ from the group component $Z$ of the record `productionPinsOf F Φ (levelOne) (heckeGen) (adelicBox F)` to $\mathbb{C}^\times$; in that record $Z$ is the full idele unit group $\top$, the measurable space is the Borel structure `glBorel`, the measure is `adelicGLHaar (Fin 2) (𝓞 F) F`, the domain is $\Phi$, the level subgroups are `levelOne` and the Hecke elements `heckeGen`.
--
--   *Character family.* A finite index type $\iota$ and families $\mu, \nu \colon \iota \to \bigl((\mathbf{A}_F)^\times \to \mathbb{C}^\times\bigr)$ of homomorphisms, subject to: unitarity ($|\mu_e(x)| = |\nu_e(x)| = 1$ for all $x$, hypotheses `_hμ`, `_hν`); triviality on principal ideles, i.e. $\mu_e$ and $\nu_e$ are idele class characters (`_hμic`, `_hνic`); continuity of $x \mapsto \mu_e(x)$ and $x \mapsto \nu_e(x)$ (`_hμc`, `_hνc`); the central compatibility $\mu_e(z)\nu_e(z) = \xi(z)$ for every $z \in Z$ (`_hμν`); an involutive matching $r \colon \iota \to \iota$ with $\mu_{r e} = \nu_e$ and $\nu_{r e} = \mu_e$ (`_hr`); and separation (`_hdist`): for $e \neq e'$ there exists an idele $x$ in the kernel [`NumberField.TateGlobal.normOneIdeles F`](def/NumberField_TateGlobalZeta.html#L16) of the module character with $\mu_e(x) \neq \mu_{e'}(x)$ or $\nu_e(x) \neq \nu_{e'}(x)$.
--
--   *Sections.* Families $\varphi_e, \psi_e \colon \mathbb{C} \to \mathrm{GL}_2(\mathbf{A}_F) \to \mathbb{C}$ (written `φf`, `ψf`) such that for all $e$ and $s$ both $\varphi_e(s)$ and $\psi_e(s)$ are induced sections for the pair of characters `etaFst (μ e) α hα s` $= \mu_e \cdot \alpha(\cdot)^{s+1/2}$ and `etaSnd (ν e) α hα s` $= \nu_e \cdot \alpha(\cdot)^{-(s+1/2)}$, that is, $f(bg) = \chi_1(b_{00})\chi_2(b_{11}) f(g)$ for every $b$ in the adelic Borel subgroup (entry $b_{10} = 0$) and every $g$ (hypotheses `_hφf`, `_hψf`). Further: joint continuity of $(s,g) \mapsto \varphi_e(s)(g)$ and of $(s,g)\mapsto \psi_e(s)(g)$ (`_hφjc`, `_hψjc`); holomorphy in $s$ for each fixed $g$ (`_hφhol`, `_hψhol`); each $\psi_e(s)$ is `IsArchKFinite` (at every infinite place $w$ its right translates under `archRowIsometrySubgroup F w` span a finite-dimensional space) and `IsKfSmooth` (its stabiliser under right translation by the kernel of `glArch` is open) (`_hψK`, `_hψsm`); a uniform archimedean type (`_hψKu`): for each $e$ and each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup F w` containing $k \mapsto \psi_e(s)(gk)$ for all $s$ and $g$; and vertical-strip decay (`_hφdec`, `_hψdec`): for each $e$, each $n \in \mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded above $m \colon \mathbb{R} \to \mathbb{R}$ with $(1+|t|)^n \,\|\varphi_e(\sigma' + it)(g)\| \le m(t)$ (respectively for $\psi_e$) whenever $|\sigma'| \le \sigma_0$, $t \in \mathbb{R}$ and $g \in C$.
--
--   *Slab profiles.* Functions $\varphi, \psi \colon \mathrm{GL}_2(\mathbf{A}_F) \to \mathbb{C}$ satisfying `IsSlabProfile F Z ξ` (hypotheses `_hφ`, `_hψ`): measurability, left invariance under all `unipotentGL2 x`, left invariance under the rational points of the Borel subgroup, the transformation rule $\varphi(\mathrm{centralScalar}(z)g) = \xi(z)\varphi(g)$ for $z \in Z$, boundedness on every slab $\|\det g\| \in [d_1,d_2]$ with $d_1 > 0$, and a height band: there are $a > 0$ and $b$ with `adelicHeight F g` $\in [a,b]$ whenever the function is non-zero at $g$. Moreover (hypotheses `_hφrep`, `_hψrep`) on every vertical line, for all real $\sigma'$ and all $g$,
--   $$\varphi(g) = \sum_e (4\pi)^{-1} \int_{\mathbb{R}} \varphi_e(\sigma' + it)(g)\,dt, \qquad \psi(g) = \sum_e (4\pi)^{-1} \int_{\mathbb{R}} \psi_e(\sigma' + it)(g)\,dt.$$
--
--   *Continued intertwining operator.* A family $Mc \colon \iota \to \mathbb{C} \to \mathrm{GL}_2(\mathbf{A}_F) \to \mathbb{C}$ such that for each $e$ and $g$ the function $s \mapsto Mc_e(s)(g)$ is meromorphic in normal form on all of $\mathbb{C}$ and agrees, for $\operatorname{Re} s > 1/2$, with the Weyl intertwining integral `weylIntertwiningIntegral` of $\psi_e(s)$ at $g$, namely $\int_{\mathbf{A}_F} \psi_e(s)\bigl(w^{-1}\,\mathrm{unipotentGL2}(x)\,g\bigr)\,dx$ with respect to `adelicAddHaar`, $w$ being `adelicWeyl` (hypothesis `_hMc`).
--
--   *Projections.* Functions $p\varphi, p\psi$ satisfying `IsAutomorphicFnAt` for the above pins and $\xi$, i.e. the condition `LsXiMemberAt` for the Borel structure, the measure `adelicGLHaar`, the domain $\Phi$, the group $Z$ and $\xi$ (`_hpφ`, `_hpψ`). Each is approximable in $L^2$ by residual functions (`_hpφc`, `_hpψc`): for every $\varepsilon > 0$ there is $q$ in `residualSpan (𝓞 F) F Z ξ`, the $\mathbb{C}$-span of the functions $g \mapsto \chi(\det g)$ for idele characters $\chi$ with $\chi(z)^2 = \xi(z)$ on $Z$, with $q$ satisfying `IsAutomorphicFnAt` and $\|p\varphi - q\|_{L^2}$ (respectively $\|p\psi - q\|_{L^2}$), computed for the pins measure restricted to $\Phi$, less than $\varepsilon$. Each is the orthogonal projection in the relevant sense (`_hpφo`, `_hpψo`): for every $h$ satisfying `IsAutomorphicFnAt` and lying in the residual span,
--   $$\int_{\Phi} \bigl(\mathrm{pseudoEisenstein}\,\varphi(g) - p\varphi(g)\bigr)\,\overline{h(g)}\,d\mu = 0,$$
--   and likewise with $\psi$ and $p\psi$, where $\mathrm{pseudoEisenstein}\,\varphi(g) = \varphi(g) + \sum_{\beta \in F}' \varphi\bigl(w\,\mathrm{unipotentGL2}(\beta)\,g\bigr)$.
--
--   *Self-dual indices.* A finite set $P \subseteq \iota$ with $e \in P \iff \mu_e = \nu_e$ (hypothesis `_hP`).
--
--   Under these hypotheses, with the measurable space taken from the pins record, the conclusion is the identity
--   $$\int_{\Phi} p\varphi(g)\,\overline{p\psi(g)}\,d\mu \;=\; \frac{c\,\mathrm{vol}(B)\,V^2\,\log(d_2/d_1)}{8}\;\sum_{e \in P} \mathrm{vol}(B)^{-1}\int_{K} \varphi_e\!\left(\tfrac12\right)(k)\;\overline{\;\lim_{s \to 1/2,\ s \neq 1/2}\ \bigl(s - \tfrac12\bigr)\,Mc_{r e}(s)(k)\;}\;dk,$$
--   in which $\mu$ is `adelicGLHaar (Fin 2) (𝓞 F) F`, $\mathrm{vol}(B)$ denotes the real number `(adelicAddHaar (𝓞 F) F) (adelicBox F)` in $\mathbb{R}$, $c$ and $V$ are the real values of the corresponding constants, the scalar prefactor is the stated real number viewed in $\mathbb{C}$, $K$ is `adelicMaximalCompact F` with measure `maximalCompactHaar F`, and the conjugated limit is `Filter.limUnder` along the punctured neighbourhood filter of $1/2$, i.e. the residue at $s = 1/2$ of $Mc_{r e}$ evaluated at $k$.
--
--   This is the residual contribution to the Parseval identity for pseudo-Eisenstein series on a determinant slab of $\mathrm{GL}_2$ over a number field: the $L^2$ pairing of the residual projections of two pseudo-Eisenstein series is expressed through residues at $s = 1/2$ of the continued Weyl intertwining operator, summed over the self-dual indices $\mu_e = \nu_e$. It is used by [`AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab`](thm.html#AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab), which combines it with the continuous-spectrum term along the unitary axis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_residualProj_mul_conj_eq_sum_integral_maximalCompact_residue_pairing_slab.lean

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

theorem AutomorphicForm.setIntegral_residualProj_mul_conj_eq_sum_integral_maximalCompact_residue_pairing_slab
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
              (adelicBox F)).μ = 0)
      (P : Finset ι) (_hP : ∀ e, e ∈ P ↔ μ e = ν e),
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
        pφ g * starRingEnd ℂ (pψ g)
      ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ =
    ((c.toReal * ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal * V.toReal ^ 2
        * Real.log (d₂ / d₁) / 8 : ℝ) : ℂ) *
    ∑ e ∈ P,
      (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        ∫ k, φf e (1 / 2 : ℂ) (k : AdelicGL2 (𝓞 F) F)
          * starRingEnd ℂ (Filter.limUnder (𝓝[≠] (1 / 2 : ℂ))
              (fun s : ℂ => (s - (1 / 2 : ℂ)) * Mc (r e) s (k : AdelicGL2 (𝓞 F) F)))
        ∂(maximalCompactHaar F) := by sorry
