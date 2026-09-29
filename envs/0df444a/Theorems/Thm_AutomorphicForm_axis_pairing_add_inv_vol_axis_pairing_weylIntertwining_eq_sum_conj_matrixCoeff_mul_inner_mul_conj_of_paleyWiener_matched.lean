-- Prove2me | Theorems.Thm_AutomorphicForm_axis_pairing_add_inv_vol_axis_pairing_weylIntertwining_eq_sum_conj_matrixCoeff_mul_inner_mul_conj_of_paleyWiener_matched
-- name    : AutomorphicForm.axis_pairing_add_inv_vol_axis_pairing_weylIntertwining_eq_sum_conj_matrixCoeff_mul_inner_mul_conj_of_paleyWiener_matched
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/d2cbfd8c-d259-57f0-9462-9522de7d302a
-- title:
--   Asymmetric axis pairing with intertwining term, matched data
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}=\mathbb{A}_K$ its adele ring, $G=\mathrm{GL}_2(\mathbb{A})$ (`AdelicGL2`), and $\mathbf{K}=$ `adelicMaximalCompact K` the subgroup of those $g\in G$ whose finite part lies in `finiteIntegralGL2` and whose component at every infinite place $w$ is a row isometry; integrals $\int_{\mathbf K}\cdots dk$ are taken against `maximalCompactHaar K`. For functions $a,b$ on $G$ write $\langle a,b\rangle=\int_{\mathbf K}a(k)\overline{b(k)}\,dk$. The character $\alpha_m$ (`αm`) is the module character of $\mathbb{A}$, i.e. `distribHaarChar` followed by $\mathbb{R}_{\ge 0}\to\mathbb{R}$, viewed as a homomorphism into $\mathbb{R}^\times$, and `hαm` asserts that its values are positive; for an idele class character $\chi$, `etaFst χ αm hαm s` $=\chi\cdot\alpha_m^{s+1/2}$ and `etaSnd χ αm hαm s` $=\chi\cdot\alpha_m^{-(s+1/2)}$. A function $\varphi$ on $G$ is an induced section for a pair $(\chi_1,\chi_2)$ (`IsInducedSection`) when $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for every $b$ in the adelic Borel subgroup (lower–left entry zero) and every $g$. The right convolution `rightConv K u f` is $g\mapsto\int_G u(gx)f(x)\,dx$ against `adelicGLHaar`, and `convOp K f u = rightConv K u f`; it is written $R(f)u$ below.
--
--   Fixed data: real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full unit group $\top\le\mathbb{A}^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and of absolute value $1$ at every idele (`hξu`); an ideal $N\subseteq\mathcal O_K$ such that every finite place whose prime divides $N$ belongs to $S_K$ (`hN`); and an archimedean type family `tysK` (a number `card w` of representations `rep w i` of the row isometry group at each infinite place $w$), whose associated cut submodule `archCutSubmodule K tysK` is $\bigcap_w\sum_i$ (type submodule of `rep w i`).
--
--   Continuous block. A countable index type $\iota_E$ is given, together with families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb{A}^\times,\mathbb{C}^\times)$ subject to: unitarity ($\|\mu_e(x)\|=\|\nu_e(x)\|=1$), triviality on $K^\times$ (`IsIdeleClassChar`), continuity of $\mu_e,\nu_e$, the product relation $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $z$, and separation: for $e\ne e'$ there is a norm-one idele $z$ (an element of [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16), the kernel of `distribHaarChar`) at which $\mu_e$ and $\mu_{e'}$, or $\nu_e$ and $\nu_{e'}$, differ. For each $e$ a number $n_E(e)$ and sections $\varphi_{e,j}(s)$, $j<n_E(e)$, are given, with the hypotheses (each quantified over $e$, $j$ and $s$): $\varphi_{e,j}(s)$ is an induced section for $(\mathrm{etaFst}(\mu_e,s),\mathrm{etaSnd}(\nu_e,s))$; it is archimedean $\mathbf K$-finite and $K_f$-smooth; $(s,g)\mapsto\varphi_{e,j}(s)(g)$ is continuous and $s\mapsto\varphi_{e,j}(s)(g)$ is entire; at each infinite place $w$ there is a single finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup K w` containing all the right-translate functions $k\mapsto\varphi_{e,j}(s)(gk)$ (uniform $\mathbf K$-finiteness); flatness, $\varphi_{e,j}(s)(k)=\varphi_{e,j}(0)(k)$ for $k\in\mathbf K$; right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; membership in `archCutSubmodule K tysK`; orthonormality $\int_{\mathbf K}\varphi_{e,i}(0)(k)\overline{\varphi_{e,j}(0)(k)}\,dk=\delta_{ij}$; and completeness on the unitary axis (`_hφEspan`): every continuous, archimedean $\mathbf K$-finite induced section for $(\mathrm{etaFst}(\mu_e,it),\mathrm{etaSnd}(\nu_e,it))$ which is right invariant under that level group and lies in the cut submodule belongs to the $\mathbb{C}$-span of the $\varphi_{e,j}(it)$. Finally, sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_{e,j},N_{e,j}$ are given, and the hypothesis `_hEE` (nine clauses) states: $O_E(e,j)$ is open and preconnected, contains the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$, $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$; both $(s,g)\mapsto E_{e,j}(s)(g)$ and $(s,g)\mapsto N_{e,j}(s)(g)$ are continuous on $O_E(e,j)\times G$; and for $\mathrm{Re}\,s>1/2$ one has $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum_{\xi\in K}\varphi_{e,j}(s)(w\,u(\xi)\,g)$ (with $w$ the image of the antidiagonal Weyl element and $u(\xi)$ the unipotent matrix with entry $\xi$) and $N_{e,j}(s)(g)=\int_{\mathbb{A}}\varphi_{e,j}(s)(w^{-1}u(x)g)\,dx$ against `adelicAddHaar`.
--
--   Test function. A function $f:G\to\mathbb{C}$ is given which is continuous, of compact support, factorizable ($f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ coming from a smooth compactly supported function of the archimedean matrix entries and $f_{\mathrm{fin}}$ locally constant of compact support), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and archimedean bi-finite of type `tysK`: $x\mapsto f(x^{-1})$ lies in `archCutSubmodule K tysK` and $f$ lies in `archDualCutSubmodule K tysK`.
--
--   Paley–Wiener block. A finite index type $\iota_P$ is given with families $\mu_P,\nu_P$ of characters of $\mathbb{A}^\times$ which are unitary, trivial on $K^\times$, and continuous, and which satisfy $\mu_P(e)(z)\,\nu_P(e)(z)=\xi_K(z)$ for every $z$ in the subgroup $Z$ of the `CarrierPins` datum `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, that subgroup being $\top$. A map $r=\,$`rP` on $\iota_P$ interchanges the two characters exactly, $\mu_P(r(e))=\nu_P(e)$ and $\nu_P(r(e))=\mu_P(e)$, and separation holds as before at norm-one ideles. Two families of sections $\hat\varphi_e(s),\hat\psi_e(s)$ are given, both induced sections for $(\mathrm{etaFst}(\mu_P(e),s),\mathrm{etaSnd}(\nu_P(e),s))$, both jointly continuous in $(s,g)$ and entire in $s$ for fixed $g$; in addition $\hat\psi_e(s)$ is archimedean $\mathbf K$-finite, $K_f$-smooth, and uniformly $\mathbf K$-finite in the sense above. The hypotheses `_hφdec` and `_hψdec` are Paley–Wiener decay: for each $e$, each $n\in\mathbb{N}$, each $\sigma_0\in\mathbb{R}$ and each compact $C\subseteq G$ there is an integrable, bounded-above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\hat\varphi_e(\sigma'+it)(g)\|\le m(t)$ (respectively with $\hat\psi_e$) for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. Sets $O_\psi(i)$ and families $E_\psi,N_\psi$ are given, with the hypothesis `_hEψ` of the same nine clauses as `_hEE`, now for $\hat\psi_i$: openness, preconnectedness, containment of the imaginary axis and of $\{\mathrm{Re}\,s>1/2\}$, analyticity and joint continuity of $E_\psi(i)$ and $N_\psi(i)$, and, for $\mathrm{Re}\,s>1/2$, the Eisenstein formula for $E_\psi(i)$ and the Weyl intertwining integral formula for $N_\psi(i)$ in terms of $\hat\psi_i(s)$. Finally a matching is given: maps $e(\cdot)=\,$`em` $:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ with $\mu_P(i)=\mu_{e(i)}\cdot\|\cdot\|^{i\tau_i}$ and $\nu_P(i)=\nu_{e(i)}\cdot(\|\cdot\|^{i\tau_i})^{-1}$, where $\|\cdot\|^{i\tau}$ denotes [`NumberField.TateGlobal.normPowChar K τ`](def/NumberField_NormPowChar.html#L22), $x\mapsto(\mathrm{ideleNorm}\,x)^{\mathrm{i}\tau}$.
--
--   Conclusion. Fix $i\in\iota_P$ and $t\in\mathbb{R}$, put $v=\big(\mathrm{adelicAddHaar}(\mathrm{adelicBox}\,K)\big)_{\mathbb{R}}\in\mathbb{C}$ (the real volume of the adelic box, coerced to $\mathbb{C}$) and $t_E=(t+\tau_i)\,\mathrm{i}$. Then
--   $$\big\langle\hat\varphi_i(it),\,R(f)\hat\psi_i(it)\big\rangle+v^{-1}\big\langle\hat\varphi_i(it),\,R(f)\,N_\psi(r(i))(-it)\big\rangle$$
--   equals
--   $$\sum_{j<n_E(e(i))}\ \sum_{k<n_E(e(i))}\overline{\big\langle R(f)\varphi_{e(i),k}(t_E),\,\varphi_{e(i),j}(t_E)\big\rangle}\;\Big(\big\langle\hat\varphi_i(it),\varphi_{e(i),j}(t_E)\big\rangle\cdot\overline{\Big(\big\langle\hat\psi_i(it),\varphi_{e(i),k}(t_E)\big\rangle+\big\langle\hat\psi_{r(i)}(-it),\,v^{-1}N_{e(i),k}(t_E)\big\rangle\Big)}\Big),$$
--   where all pairings are the $\mathbf K$-integrals described above, $R(f)u=\,$`rightConv K u f`, and in the inner factor of the first summand the convolution is applied to $\varphi_{e(i),k}(t_E)$ while the conjugated section is $\varphi_{e(i),j}(t_E)$.
--
--   This is the two-term fold of the Eisenstein contribution at a single point $it$ of the unitary axis: the pairing of a weak Paley–Wiener section against the convolution of the strong one, together with the correction coming from the axis continuation of the Weyl intertwining integral, is expressed through the matrix coefficients of $R(f)$ in the orthonormal flat basis $\varphi_{e(i),j}$ at the matched point $(t+\tau_i)\mathrm{i}$. It is the pointwise input for the swapped form of the identity and for its integrated version over the axis, which assemble the Eisenstein part of the spectral comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_axis_pairing_add_inv_vol_axis_pairing_weylIntertwining_eq_sum_conj_matrixCoeff_mul_inner_mul_conj_of_paleyWiener_matched.lean

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

theorem AutomorphicForm.axis_pairing_add_inv_vol_axis_pairing_weylIntertwining_eq_sum_conj_matrixCoeff_mul_inner_mul_conj_of_paleyWiener_matched
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
      (i : ιP) (t : ℝ),
    let vol : ℂ := (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)
    let tE : ℂ := (((t + τ i : ℝ) : ℂ)) * Complex.I
    (∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
      vol⁻¹ * ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
    ∑ j : Fin (nE (em i)), ∑ k' : Fin (nE (em i)),
      conj (∫ k, rightConv K (φE (em i) k' tE) f (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j tE (k : AdelicGL2 (𝓞 K) K))
          ∂(maximalCompactHaar K)) *
      ((∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
        conj ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) k' tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
          ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj (vol⁻¹ * NE (em i) k' tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) := by sorry
