-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener
-- name    : AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/eb88dcb7-8616-571b-b647-299f195991a8
-- title:
--   Axis Parseval identity for the pair (φ, R(f)ψ)
-- statement:
--   Throughout, $K$ is a number field and $\alpha,\beta$ are reals with $0<\alpha$ and $\alpha<\beta$; $\Phi_0 :=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) denotes the truncation domain attached to $(\alpha,\beta)$, and `pins` denotes the carrier data `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, whose measurable space and measure on $\mathrm{GL}_2(\mathbb{A}_K)$ are `glBorel` and `adelicGLHaar`, whose domain is $\Phi_0$, whose central subgroup is $Z = \top$ (the full idele unit group), whose level groups are $M \mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, whose Hecke generators are the `heckeGen`, and whose additive measure is `adelicAddHaar` conditioned on the box `adelicBox K`.
--
--   Central datum. $S_K$ is a finite set of finite places of $K$; $\xi_K$ is a monoid homomorphism from $\top \le (\mathbb{A}_K)^{\times}$ to $\mathbb{C}^{\times}$, assumed continuous as a function of the underlying idele (`hξc`), trivial on the image of $K^{\times}$ (`hξt`), and of absolute value $1$ everywhere (`hξu`). $N$ is an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`), and `tysK` is an `ArchTypeFamily K`, i.e. a finite family of representations of the archimedean row-isometry groups at each infinite place. The character $\alpha_m$ is the homomorphism $(\mathbb{A}_K)^{\times} \to \mathbb{R}^{\times}$ obtained from `distribHaarChar (AdeleRing (𝓞 K) K)` followed by $\mathbb{R}_{\ge 0} \to \mathbb{R}$, taken into the units; `hαm` asserts that its values are positive.
--
--   Measure-theoretic constants. A constant $c \in [0,\infty]$, neither $0$ nor $\infty$, is given together with the Iwasawa disintegration `_hc`: for every measurable $H : \mathrm{GL}_2(\mathbb{A}_K) \to [0,\infty]$,
--   $$\int^{-} H \, d(\mathrm{adelicGLHaar}) = c \int^{-}_{x}\int^{-}_{u}\int^{-}_{t}\int^{-}_{k} H\bigl(n(x)\, z(u)\, \mathrm{diag}(t,1)\, k\bigr)\,\lVert t\rVert^{-1},$$
--   the inner integrals being over the maximal compact subgroup with `maximalCompactHaar`, over ideles with `idelicHaar` twice, and the outer one over $\mathbb{A}_K$ with `adelicAddHaar`; here $n(x)$ is the unipotent matrix `unipotentGL2 x`, $z(u)$ the central scalar, $\mathrm{diag}(t,1)$ is `diagOne t`, and $\lVert t \rVert$ is the idele norm. Further, $D$ is a measurable subset of the ideles which is a fundamental domain for the subgroup of principal ideles with respect to `idelicHaar`, and $V \in [0,\infty]$ is neither $0$ nor $\infty$ and realises the norm disintegration `_hV`: $\int^{-}_{z \in D} f(\lVert z\rVert) = V \int^{-}_{y>0} f(y)\,y^{-1}$ for every measurable $f : \mathbb{R} \to [0,\infty]$.
--
--   The character family. $\iota_P$ is a finite type and $\mu_P, \nu_P : \iota_P \to \mathrm{Hom}((\mathbb{A}_K)^{\times}, \mathbb{C}^{\times})$. Each $\mu_P e$ and $\nu_P e$ is unitary (absolute value $1$ at every idele) and an idele class character (trivial on the image of $K^{\times}$), each $\mu_P e$ and each $\nu_P e$ is continuous, and $\mu_P e \cdot \nu_P e = \xi_K$ on all of $Z = \top$ (`_hμν`). A map $r_P : \iota_P \to \iota_P$ interchanges the two families, $\mu_P(r_P e) = \nu_P e$ and $\nu_P(r_P e) = \mu_P e$, and the family is separated (`_hdist`): for $e \ne e'$ there is a norm-one idele at which either the $\mu$'s or the $\nu$'s differ.
--
--   The Paley–Wiener data. $\varphi_f, \psi_f : \iota_P \to \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy, for all $e$ and $s$, the induced-section identity for the characters $\eta_1 = \mu_P e \cdot \lVert\cdot\rVert^{s+1/2}$ and $\eta_2 = \nu_P e \cdot \lVert\cdot\rVert^{-(s+1/2)}$, that is $\varphi_f\,e\,s\,(bg) = \eta_1(b_{00})\eta_2(b_{11})\,\varphi_f\,e\,s\,(g)$ for $b$ in the adelic Borel subgroup (matrices with vanishing $(1,0)$ entry), and likewise for $\psi_f$. Both families are jointly continuous in $(s,g)$ and entire in $s$ for each fixed $g$. In addition each $\psi_f\,e\,s$ is archimedean $K$-finite and `IsKfSmooth` (a smooth vector for right translation by the finite-adelic subgroup), and `_hψKu` provides, for each $e$ and each infinite place $w$, a single finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup at $w$ containing all the functions $k \mapsto \psi_f\,e\,s\,(gk)$, uniformly in $s$ and $g$. The vertical-decay hypotheses `_hφdec`, `_hψdec` state that for each index $e$, each $n \in \mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded majorant $m : \mathbb{R} \to \mathbb{R}$ with $(1+|t|)^n \lVert \varphi_f\,e\,(\sigma'+it)\,g\rVert \le m(t)$ for $|\sigma'| \le \sigma_0$, $t \in \mathbb{R}$ and $g \in C$, and correspondingly for $\psi_f$.
--
--   The profiles. $\varphi, \psi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ are slab profiles for $Z = \top$ and $\xi_K$: measurable, invariant under left multiplication by unipotents $n(x)$ and by global points of the Borel subgroup, $\xi_K$-equivariant under left multiplication by central scalars, bounded on each slab $\{\lVert\det g\rVert \in [d_1,d_2]\}$ with $d_1>0$, and supported in a band $a \le \mathrm{adelicHeight}(g) \le b$ with $a>0$. The inversion hypotheses `_hφrep`, `_hψrep` assert that for every real $\sigma'$ and every $g$,
--   $$\varphi(g) = \sum_{e} (4\pi)^{-1} \int_{\mathbb{R}} \varphi_f\,e\,(\sigma'+it)\,g \, dt, \qquad \psi(g) = \sum_{e} (4\pi)^{-1} \int_{\mathbb{R}} \psi_f\,e\,(\sigma'+it)\,g \, dt .$$
--
--   Continuations for $\psi$. Sets $O_\psi : \iota_P \to \mathcal{P}(\mathbb{C})$ and functions $E_\psi, N_\psi : \iota_P \to \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ are given such that, for each $i$: $O_\psi i$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$ the functions $s \mapsto E_\psi\,i\,s\,g$ and $s \mapsto N_\psi\,i\,s\,g$ are analytic on a neighbourhood of $O_\psi i$; both are continuous in $(s,g)$ on $O_\psi i \times \mathrm{univ}$; for $\mathrm{Re}\,s > 1/2$ one has $E_\psi\,i\,s\,g = \psi_f\,i\,s\,g + \sum_{\xi \in K}' \psi_f\,i\,s\,(w\,n(\xi)\,g)$ with $w$ the adelic Weyl element, and $N_\psi\,i\,s\,g = \int_{\mathbb{A}_K} \psi_f\,i\,s\,(w^{-1} n(x) g)\, dx$ with respect to `adelicAddHaar`.
--
--   The test function. $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ is continuous with compact support, factorizable (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and archimedean bi-finite for the type family `tysK`.
--
--   The residual projections. $p_\varphi$ is `IsAutomorphicFnAt K pins ξK`-automorphic, it is approximable: for each $\varepsilon>0$ there is an element $q$ of the residual span — the $\mathbb{C}$-span of the functions $g \mapsto \chi(\det g)$ for characters $\chi$ with $\chi^2 = \xi_K$ on $Z$ — which is itself automorphic for the same pins and character and satisfies $\lVert p_\varphi - q\rVert_{L^2(\Phi_0)} < \varepsilon$ for the restriction of `adelicGLHaar` to $\Phi_0$; and it is orthogonal in the sense that for every automorphic $h$ lying in that residual span,
--   $$\int_{\Phi_0} \bigl(\mathrm{pseudoEisenstein}\,\varphi\,(g) - p_\varphi(g)\bigr)\overline{h(g)}\, d(\mathrm{adelicGLHaar}) = 0 ,$$
--   where $\mathrm{pseudoEisenstein}\,\varphi\,(g) = \varphi(g) + \sum_{b \in K}' \varphi(w\,n(b)\,g)$. The same three conditions are imposed on $p_\psi$ relative to $\psi$.
--
--   Conclusion. Writing $R(f)u :=$ `convOp K f u`, the right convolution $g \mapsto \int u(gx) f(x)\, dx$ against `adelicGLHaar`, and $v := (\mathrm{adelicAddHaar}(\mathrm{adelicBox}\,K)).\mathrm{toReal}$, the assertion is the identity
--   $$\int_{\Phi_0} \mathrm{pseudoEisenstein}\,\varphi \cdot \overline{R(f)\,\mathrm{pseudoEisenstein}\,\psi} \; - \; \int_{\Phi_0} p_\varphi \cdot \overline{R(f)\,p_\psi}$$
--   $$= \frac{c_{\mathbb{R}}\, v\, V_{\mathbb{R}}^2 \log(\beta/\alpha)}{16\pi} \sum_{i \in \iota_P} \int_{\mathbb{R}} \Bigl( \int_{K_{\max}} \varphi_f\,i\,(it)\,k \cdot \overline{R(f)\bigl(\psi_f\,i\,(it)\bigr)(k)}\, dk \;+\; v^{-1} \int_{K_{\max}} \varphi_f\,i\,(it)\,k \cdot \overline{R(f)\bigl(N_\psi\,(r_P i)\,(-it)\bigr)(k)}\, dk \Bigr) dt,$$
--   both integrals over $\Phi_0$ being taken against `adelicGLHaar`, the inner integrals over the adelic maximal compact subgroup against `maximalCompactHaar`, and $c_{\mathbb{R}}$, $V_{\mathbb{R}}$ denoting the real numbers underlying $c$ and $V$; the scalar factor is the real number displayed, coerced to $\mathbb{C}$.
--
--   This is the Parseval identity on the unitary axis for pseudo-Eisenstein series, in the form obtained by transporting the Paley–Wiener datum of $\psi$ through right convolution by a test function $f$: it expresses the defect between the truncated inner product of $\theta_\varphi$ with $R(f)\theta_\psi$ and that of their residual projections as an explicit integral over the imaginary axis, with a main term and a term involving the continued intertwining integral at the swapped index. It serves the continuous-spectrum bookkeeping in the spectral decomposition of the convolution operators on the truncated domain, and is used to produce the corresponding statement for continuous families of projections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_convOp_pseudoEisenstein_sub_eq_mul_sum_integral_axis_pairing_convOp_of_paleyWiener
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (c : ℝ≥0∞) (_hc0 : c ≠ 0) (_hcT : c ≠ ∞)
      (_hc : ∀ H : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable H →
        ∫⁻ g, H g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                H (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K))
      (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (φf ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK φ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hφrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (Oψ : ιP → Set ℂ) (Eψ Nψ : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ : ∀ i : ιP,
      IsOpen (Oψ i) ∧ IsPreconnected (Oψ i) ∧ {s : ℂ | s.re = 0} ⊆ (Oψ i) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (Oψ i) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ i s g) (Oψ i)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ i s g) (Oψ i)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ i s g = ψf i s g + ∑' ξ : K, ψf i s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ i s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf i s) g))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀
      (pφ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpφ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pφ)
      (_hpφc : ∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (pφ - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpφo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (AutomorphicForm.pseudoEisenstein K φ g - pφ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (pψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ)
      (_hpψc : ∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (pψ - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
,
    (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        AutomorphicForm.pseudoEisenstein K φ g * conj (convOp K f (AutomorphicForm.pseudoEisenstein K ψ) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        pφ g * conj (convOp K f pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
    ((c.toReal * ((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal * V.toReal ^ 2
        * Real.log (β / α) / (16 * Real.pi) : ℝ) : ℂ) *
    ∑ i : ιP, ∫ t : ℝ,
      ((∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by sorry
