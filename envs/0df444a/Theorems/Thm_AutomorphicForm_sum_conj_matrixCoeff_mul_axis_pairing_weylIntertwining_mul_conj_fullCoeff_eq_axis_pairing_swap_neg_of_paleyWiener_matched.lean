-- Prove2me | Theorems.Thm_AutomorphicForm_sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched
-- name    : AutomorphicForm.sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b8a6d829-3da3-5c8b-95a7-f34c9fa34039
-- title:
--   Involution identity for the matched Paley–Wiener fold
-- statement:
--   Throughout, $K$ is a number field, $\alpha,\beta$ are reals with $0<\alpha<\beta$, $S_K$ is a finite set of finite places of $K$, and $\xi_K$ is a homomorphism from the full subgroup $\top$ of the idele units of $K$ to $\mathbb{C}^\times$ subject to three conditions: continuity of the induced function on ideles (`hξc`), triviality on the image of $K^\times$ under `Units.map (algebraMap K (AdeleRing (𝓞 K) K))` (`hξt`), and $|\xi_K(z)|=1$ for all $z$ (`hξu`). Further global data: an ideal $N$ of $\mathcal O_K$ with the property that every place dividing $N$ lies in $S_K$ (`hN`), and an archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place $w$ a finite list of representations of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$. The character $\alpha_m$ is the modulus character of the adele ring, namely `distribHaarChar` followed by $\mathbb{R}_{\ge 0}\to\mathbb{R}$, viewed as a homomorphism into $\mathbb{R}^\times$, and `hαm` asserts its positivity. The measure-theoretic structure on the adeles is the Borel one, `adeleBorel`. Below, $\mathbf{K}=$ `adelicMaximalCompact K` is the subgroup of $g\in\mathrm{GL}_2(\mathbb{A}_K)$ whose finite part is integral and whose component at each infinite place is a row isometry, and all pairings are taken with respect to `maximalCompactHaar K`: $\langle a,b\rangle=\int_{\mathbf K}a(k)\overline{b(k)}$. For $u$ a function on $\mathrm{GL}_2(\mathbb{A}_K)$, $R(f)u=$ `rightConv K u f`, i.e. $g\mapsto\int u(gx)f(x)$ against `adelicGLHaar`; `convOp K f u` is the same function. Finally $v=$ the real number $(\,$`adelicAddHaar (𝓞 K) K`$)(\,$`adelicBox K`$)$, and $\mathrm{I}$ denotes the imaginary unit.
--
--   Continuous block data. A countable index type $\iota_E$, families $\mu,\nu:\iota_E\to\widehat{\mathbb{A}_K^\times}$ with: each $\mu e,\nu e$ unitary (`IsUnitaryChar`) and trivial on $K^\times$ (`IsIdeleClassChar`), continuous, satisfying $\mu e\cdot\nu e=\xi_K$ pointwise, and separated in the sense that distinct $e\neq e'$ are distinguished by some idele of norm one (`_hdist`, via [`NumberField.TateGlobal.normOneIdeles`](def/NumberField_TateGlobalZeta.html#L16)). For each $e$ a rank $n_E(e)$ and a family $\varphi_{e,j}(s)$, $j\in\mathrm{Fin}(n_E(e))$, $s\in\mathbb{C}$, of functions on $\mathrm{GL}_2(\mathbb{A}_K)$, with the hypotheses, grouped and summarised here: each $\varphi_{e,j}(s)$ is an induced section for the pair $(\mu e\cdot\alpha_m^{s+1/2},\ \nu e\cdot\alpha_m^{-(s+1/2)})$ in the sense of `IsInducedSection` (equivariance $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel); it is archimedean $K$-finite and $K_f$-smooth; the map $(s,g)\mapsto\varphi_{e,j}(s)(g)$ is continuous and $s\mapsto\varphi_{e,j}(s)(g)$ is entire; at each infinite place the right translates lie in one fixed finite-dimensional space of functions on the row-isometry subgroup, uniformly in $s$ and $g$ (`_hφEKu`); the restriction to $\mathbf K$ is independent of $s$ (`_hφEflat`); right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; membership in `archCutSubmodule K tysK`; orthonormality $\langle\varphi_{e,i}(0),\varphi_{e,j}(0)\rangle=\delta_{ij}$; and completeness (`_hφEspan`): on the imaginary axis every induced section for the same character pair which is continuous, archimedean $K$-finite, invariant under that level group and of the prescribed archimedean type lies in the $\mathbb{C}$-span of the $\varphi_{e,j}(t\mathrm{I})$.
--
--   Axis continuation for the blocks. Sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_{e,j},N_{e,j}$ of $(s,g)$ such that (nine clauses, `_hEE`) $O_E(e,j)$ is open and preconnected and contains both the line $\operatorname{Re}s=0$ and the half-plane $\operatorname{Re}s>1/2$; $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$ for each $g$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$; and for $\operatorname{Re}s>1/2$ one has the Eisenstein expansion $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum_{\xi\in K}\varphi_{e,j}(s)(w\,u(\xi)g)$, with $w=$ `adelicWeyl` and $u(\xi)=$ `unipotentGL2` of the image of $\xi$, and $N_{e,j}(s)(g)=$ `weylIntertwiningIntegral` of $\varphi_{e,j}(s)$, namely $\int_{\mathbb{A}_K}\varphi_{e,j}(s)(w^{-1}u(x)g)$ against `adelicAddHaar`.
--
--   Test function. A continuous, compactly supported $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is factorizable (`IsFactorizableTestFn`: a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and archimedean bi-finite for $\mathrm{tys}_K$ (`IsArchBiFinite`).
--
--   Matched Paley–Wiener datum. A finite index type $\iota_P$, characters $\mu_P,\nu_P$ which are unitary, trivial on $K^\times$ and continuous, with $\mu_P(e)(z)\nu_P(e)(z)=\xi_K(z)$ for $z$ in the subgroup $Z$ of the record `productionPinsOf K (canonicalTruncationDomain K α β) (M\mapsto principalLevel\ M\sqcap finiteAdelicGL2Subgroup) heckeGen (adelicBox K)` — that subgroup being $\top$, so the identity holds for all ideles, the truncation domain, level family, Hecke generators and box entering only as the remaining fields of the record. An exact swap $r_P:\iota_P\to\iota_P$ with $\mu_P(r_Pe)=\nu_P(e)$ and $\nu_P(r_Pe)=\mu_P(e)$, and a separation hypothesis on norm-one ideles as before. Families $\hat\varphi_e(s),\hat\psi_e(s)$, both induced sections for $(\mu_P e\cdot\alpha_m^{s+1/2},\nu_P e\cdot\alpha_m^{-(s+1/2)})$, jointly continuous in $(s,g)$ and entire in $s$; $\hat\psi_e(s)$ is archimedean $K$-finite, $K_f$-smooth and of uniformly bounded archimedean $K$-type; and both families satisfy vertical-strip decay (`_hφdec`, `_hψdec`): for every index, every $n\in\mathbb{N}$, every $\sigma_0$ and every compact $C$ there is an integrable, bounded $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\hat\varphi_e(\sigma'+t\mathrm{I})(g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, $t\in\mathbb{R}$, $g\in C$, and likewise for $\hat\psi$. Sets $O_\psi(i)$ and functions $E'_i,N'_i$ satisfy the same nine-clause package `_hEψ` relative to $\hat\psi_i$.
--
--   Matching and growth. Maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ with $\mu_P(i)=\mu(\mathrm{em}\,i)\cdot$`normPowChar K (τ i)` and $\nu_P(i)=\nu(\mathrm{em}\,i)\cdot($`normPowChar K (τ i)`$)^{-1}$, where `normPowChar K t` sends an idele to the $\mathrm{I}t$-th power of its norm; and polynomial growth on the axis: for each $i$, respectively each $(e,j)$, there are $A$ and $n$ with $\|N'_i(t\mathrm{I})(k)\|\le A(1+|t|)^n$, respectively $\|N_{e,j}(t\mathrm{I})(k)\|\le A(1+|t|)^n$, for all $t\in\mathbb{R}$ and all $k\in\mathbf K$.
--
--   Conclusion. For every index $i\in\iota_P$ and every $t\in\mathbb{R}$, writing $e=\mathrm{em}\,i$ and $s_i=(t+\tau_i)\mathrm{I}$,
--   $$\sum_{j}\sum_{k'}\overline{\langle R(f)\varphi_{e,k'}(s_i),\,\varphi_{e,j}(s_i)\rangle}\cdot\Big(\big\langle \hat\varphi_{r_Pi}(-t\mathrm{I}),\,v^{-1}N_{e,j}(s_i)\big\rangle\cdot\overline{\big\langle\hat\psi_i(t\mathrm{I}),\varphi_{e,k'}(s_i)\big\rangle+\big\langle\hat\psi_{r_Pi}(-t\mathrm{I}),\,v^{-1}N_{e,k'}(s_i)\big\rangle}\Big)$$
--   equals
--   $$\big\langle \hat\varphi_{r_Pi}((-t)\mathrm{I}),\,R(f)\hat\psi_{r_Pi}((-t)\mathrm{I})\big\rangle+v^{-1}\big\langle \hat\varphi_{r_Pi}((-t)\mathrm{I}),\,R(f)N'_{r_P(r_Pi)}(t\mathrm{I})\big\rangle,$$
--   both sums over $j,k'\in\mathrm{Fin}(n_E(e))$. On the left the argument $-t\mathrm{I}$ occurs as $-(t\mathrm{I})$ and on the right as the product of the coercion of $-t$ with $\mathrm{I}$; in the last term the continuation $N'$ is taken at the index $r_P(r_Pi)$ and at the point $-((-t)\mathrm{I})=t\mathrm{I}$. The factor $v^{-1}$ is the inverse of the real volume of `adelicBox K`, inserted inside the conjugated slot of the relevant pairing.
--
--   This is the cross-term, or involution, identity for the continuous (Eisenstein) contribution in the adelic Kuznetsov-type expansion on $\mathrm{GL}_2$: the left-hand side collects the mixed terms of the spectral fold at the pair $(i,t)$ expanded in the orthonormal block basis $\varphi_{e,j}$, and the right-hand side identifies them with the unfolded pairing at the partner point $(r_Pi,-t)$ obtained from the exact swap of the two inducing characters. It is used by [`AutomorphicForm.sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched`](thm.html#AutomorphicForm.sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched), where the re-indexing $(i,t)\mapsto(r_Pi,-t)$ turns the symmetric two-term fold into twice the asymmetric one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched.lean

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

theorem AutomorphicForm.sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched
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
      (i : ιP) (t : ℝ),
    ∑ j : Fin (nE (em i)), ∑ k' : Fin (nE (em i)),
      conj (∫ k, rightConv K (φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)) *
      ((∫ k, φf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
        conj ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
            ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) =
    (∫ k, φf (rP i) (((-t : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (ψf (rP i) (((-t : ℝ) : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * ∫ k, φf (rP i) (((-t : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (Nψ (rP (rP i)) (-(((-t : ℝ) : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by sorry
