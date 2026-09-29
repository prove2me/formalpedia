-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched
-- name    : AutomorphicForm.integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/6859d875-7ffc-5793-9dd5-78381fc81e95
-- title:
--   Integrability of the axis pairings of a matched Paley–Wiener datum
-- statement:
--   Ambient data. Let $K$ be a number field, let $\alpha,\beta\in\mathbb R$ satisfy $0<\alpha$ and $\alpha<\beta$, let `SK` be a finite set of finite places of $K$, and let $\xi_K$ be a homomorphism from the full subgroup $\top$ of $(\mathbb A_K)^\times$ to $\mathbb C^\times$ subject to three hypotheses: `hξc`, that $z\mapsto\xi_K(z)\in\mathbb C$ is continuous; `hξt`, that $\xi_K(z)=1$ for every $z$ in the image of $K^\times$ under `Units.map (algebraMap K (AdeleRing (𝓞 K) K))`; and `hξu`, that $\lVert\xi_K(z)\rVert=1$ for all $z$. Let $N$ be an ideal of $\mathcal O_K$ with `hN`: every finite place $v$ whose ideal divides $N$ lies in `SK`. Let `tysK : ArchTypeFamily K` be an archimedean type family, that is, a number `card w` for each infinite place $w$ together with that many representations `rep w i` of the row-isometry group of $K_w$ (each packaged as an `ArchRepAt`). Write $\alpha_m$ for the character of $(\mathbb A_K)^\times$ with values in $\mathbb R^\times$ obtained from the distributive Haar character of the adele ring followed by $\mathbb R_{\ge 0}\to\mathbb R$, and let `hαm` assert that $\alpha_m$ takes positive values; the adeles carry their Borel $\sigma$-algebra. Throughout, for a character $\chi$ the pair `etaFst χ αm hαm s` and `etaSnd χ αm hαm s` denotes $\chi\cdot\alpha_m^{\,s+1/2}$ and $\chi\cdot\alpha_m^{-(s+1/2)}$, and `IsInducedSection` for a pair $(\chi_1,\chi_2)$ means $\varphi(bg)=\chi_1(b_{00})\chi_2(b_{11})\varphi(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (lower-left entry zero).
--
--   The continuous block family. Let $\iota_E$ be a countable type and $\mu,\nu:\iota_E\to\operatorname{Hom}((\mathbb A_K)^\times,\mathbb C^\times)$, subject to the character hypotheses: each $\mu_e,\nu_e$ is unitary ($\lVert\chi(x)\rVert=1$ for all ideles $x$) and an idele-class character (trivial on the image of $K^\times$), the associated $\mathbb C$-valued functions are continuous, $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $e$ and all $z$, and `_hdist`: for $e\neq e'$ there is $z$ in the norm-one ideles (the kernel of the distributive Haar character) with $\mu_e(z)\neq\mu_{e'}(z)$ or $\nu_e(z)\neq\nu_{e'}(z)$. Let $n_E:\iota_E\to\mathbb N$ and let $\varphi_{E,e,j}(s)$, for $j<n_E(e)$, be functions on $\mathrm{GL}_2(\mathbb A_K)$ depending on $s\in\mathbb C$, subject to the block hypotheses: `_hφE`, $\varphi_{E,e,j}(s)$ is an induced section for $(\mu_e\alpha_m^{s+1/2},\nu_e\alpha_m^{-(s+1/2)})$; `_hφEK`, archimedean $K$-finiteness at every infinite place (the right translates under the archimedean row-isometry subgroup span a finite-dimensional space); `_hφEf`, smoothness for the finite-adelic subgroup (the kernel of `glArch`); `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for each fixed $g$; `_hφEKu`, a single finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup at each place containing all the translates $k\mapsto\varphi_{E,e,j}(s)(gk)$, uniformly in $s$ and $g$; `_hφEflat`, $\varphi_{E,e,j}(s)(k)=\varphi_{E,e,j}(0)(k)$ for $k$ in the maximal compact `adelicMaximalCompact K`; `_hφElev`, right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; `_hφEty`, membership in `archCutSubmodule K tysK`, the intersection over infinite places of the sums of the type submodules attached to `tysK`; `_hφEon`, orthonormality $\int_{\mathbf K}\varphi_{E,e,i}(0)(k)\overline{\varphi_{E,e,j}(0)(k)}\,dk=\delta_{ij}$ against `maximalCompactHaar K`; and `_hφEspan`, that every $\varphi_0$ which is an induced section for $(\mu_e\alpha_m^{it+1/2},\nu_e\alpha_m^{-(it+1/2)})$, continuous, archimedean $K$-finite, invariant under the above level subgroup and lying in `archCutSubmodule K tysK`, belongs to the $\mathbb C$-span of the $\varphi_{E,e,j}(it)$. Finally let $O_{E,e,j}\subseteq\mathbb C$ and $E_{E,e,j},N_{E,e,j}$ be given, with `_hEE` the nine-clause package: $O_{E,e,j}$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_{E,e,j}(s)(g)$ and $s\mapsto N_{E,e,j}(s)(g)$ are analytic on a neighbourhood of $O_{E,e,j}$; both are continuous on $O_{E,e,j}\times\mathrm{GL}_2(\mathbb A_K)$ jointly; and for $\operatorname{Re}s>1/2$ one has $E_{E,e,j}(s)(g)=\varphi_{E,e,j}(s)(g)+\sum_{\xi\in K}\varphi_{E,e,j}(s)\big(w\,u(\xi)\,g\big)$, with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix with upper-right entry $\xi$, and $N_{E,e,j}(s)(g)=\int_{\mathbb A_K}\varphi_{E,e,j}(s)\big(w^{-1}u(x)g\big)\,dx$ against the additive adelic Haar measure.
--
--   The test function. Let $f:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ be continuous with compact support and, in addition, factorizable in the sense of `IsFactorizableTestFn` (a product of an archimedean factor given by a smooth compactly supported function of the matrix entries in mixed space with a locally constant compactly supported factor on $\mathrm{GL}_2$ of the finite adeles), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and archimedean bi-finite for `tysK`, i.e. $g\mapsto f(g^{-1})$ lies in `archCutSubmodule K tysK` and $f$ lies in `archDualCutSubmodule K tysK`.
--
--   The finite matched Paley–Wiener datum. Let $\iota_P$ be a finite type with characters $\mu_P,\nu_P:\iota_P\to\operatorname{Hom}((\mathbb A_K)^\times,\mathbb C^\times)$, subject to: unitarity and the idele-class condition for all $\mu_{P,e},\nu_{P,e}$, continuity of the associated $\mathbb C$-valued functions (for $\mu_P$ and, further on, for $\nu_P$); `_hμν`, $\mu_{P,e}(z)\nu_{P,e}(z)=\xi_K(z)$ for every $z$ in the subgroup component `Z` of the `CarrierPins` record `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, that component being the full subgroup $\top$ of the idele units; a map $r_P:\iota_P\to\iota_P$ with `_hr`: $\mu_P(r_P e)=\nu_{P,e}$ and $\nu_P(r_P e)=\mu_{P,e}$; and `_hdist`: distinct indices are separated by $\mu_P$ or $\nu_P$ at some norm-one idele. Let $\varphi_{f,e}(s),\psi_{f,e}(s)$ be functions on $\mathrm{GL}_2(\mathbb A_K)$ subject to: `_hφf` and `_hψf`, both are induced sections for $(\mu_{P,e}\alpha_m^{s+1/2},\nu_{P,e}\alpha_m^{-(s+1/2)})$; joint continuity in $(s,g)$ for both; holomorphy in $s$ for each $g$ for both; for $\psi_f$ in addition archimedean $K$-finiteness, smoothness for the finite-adelic subgroup, and a uniform finite-dimensional subspace $W$ for the archimedean translates at each infinite place; and the vertical-strip decay hypotheses `_hφdec` and `_hψdec`: for each index $e$, each $n\in\mathbb N$, each $\sigma_0\in\mathbb R$ and each compact $C\subseteq\mathrm{GL}_2(\mathbb A_K)$ there is an integrable, bounded-above majorant $m:\mathbb R\to\mathbb R$ with $(1+|t|)^n\lVert\varphi_{f,e}(\sigma'+it)(g)\rVert\le m(t)$, respectively the same bound for $\psi_{f,e}$, whenever $|\sigma'|\le\sigma_0$, $t\in\mathbb R$ and $g\in C$. Let $O_{\psi,i}$, $E_{\psi,i}$, $N_{\psi,i}$ be given with `_hEψ` the same nine-clause package as `_hEE`, now with $\psi_{f,i}$ in place of $\varphi_{E,e,j}$: openness, preconnectedness, containment of the imaginary axis and of $\{\operatorname{Re}s>1/2\}$, analyticity of $s\mapsto E_{\psi,i}(s)(g)$ and $s\mapsto N_{\psi,i}(s)(g)$ on a neighbourhood of $O_{\psi,i}$, joint continuity on $O_{\psi,i}\times\mathrm{GL}_2(\mathbb A_K)$, and, for $\operatorname{Re}s>1/2$, the Eisenstein-type sum and the Weyl intertwining integral formulas for $E_{\psi,i}$ and $N_{\psi,i}$. The two families are matched by $em:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb R$ through `_hem`: $\mu_{P,i}=\mu_{em(i)}\cdot\chi_{\tau_i}$ and $\nu_{P,i}=\nu_{em(i)}\cdot\chi_{\tau_i}^{-1}$, where $\chi_t$ is the character $x\mapsto\lvert x\rvert^{\,\mathrm it}$ given by [`NumberField.TateGlobal.normPowChar K t`](def/NumberField_NormPowChar.html#L22). Finally, the growth hypotheses `_hNψ` and `_hNE` require, for each $i\in\iota_P$ and each pair $(e,j)$, constants $A\in\mathbb R$ and $n\in\mathbb N$ with $\lVert N_{\psi,i}(it)(k)\rVert\le A(1+|t|)^n$, respectively $\lVert N_{E,e,j}(it)(k)\rVert\le A(1+|t|)^n$, for all $t\in\mathbb R$ and all $k$ in the maximal compact.
--
--   Conclusion. For every index $i\in\iota_P$, the function of $t\in\mathbb R$
--   $$t\longmapsto\int_{\mathbf K}\varphi_{f,i}(it)(k)\,\overline{\big(R(f)\psi_{f,i}(it)\big)(k)}\,dk\;+\;\mathrm{vol}(\mathcal B)^{-1}\int_{\mathbf K}\varphi_{f,i}(it)(k)\,\overline{\big(R(f)N_{\psi,r_P(i)}(-it)\big)(k)}\,dk$$
--   is integrable with respect to Lebesgue measure on $\mathbb R$. Here $\mathbf K$ is `adelicMaximalCompact K` with the Haar measure `maximalCompactHaar K`, $R(f)u=$ `convOp K f u` is the right convolution $g\mapsto\int u(gx)f(x)\,dx$ against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb A_K)$, and $\mathrm{vol}(\mathcal B)$ is the real number `((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal`, regarded as a complex number and inverted; the spectral parameters are $s=it$ in the first term and $s=-it$, at the swapped index $r_P(i)$, in the second.
--
--   This is the $L^1$ input for the two-term fold on the unitary axis in the continuous-spectrum (Eisenstein) part of the $\mathrm{GL}_2$ trace-formula computation over a number field: it is what makes the $dt$-integrals of the axis pairings absolutely convergent, so that they may be split and re-indexed. It is used by [`AutomorphicForm.sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched`](thm.html#AutomorphicForm.sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched.lean

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
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched
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
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀
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
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hNψ : ∀ (i : ιP), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (_hNE : ∀ (e : ιE) (j : Fin (nE e)), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (i : ιP),
    Integrable (fun t : ℝ =>
      (∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by sorry
