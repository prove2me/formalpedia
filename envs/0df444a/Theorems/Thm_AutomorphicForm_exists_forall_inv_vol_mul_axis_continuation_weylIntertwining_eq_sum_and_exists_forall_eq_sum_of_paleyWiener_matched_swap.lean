-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_inv_vol_mul_axis_continuation_weylIntertwining_eq_sum_and_exists_forall_eq_sum_of_paleyWiener_matched_swap
-- name    : AutomorphicForm.exists_forall_inv_vol_mul_axis_continuation_weylIntertwining_eq_sum_and_exists_forall_eq_sum_of_paleyWiener_matched_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/a84d2fb0-0004-5df3-8770-d39260779d31
-- title:
--   Span transport between normalised axis continuation and swapped block
-- statement:
--   Throughout, $K$ is a number field. The data consist of: reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a finite set $S_K$ of finite places of $K$; a character $\xi_K$ of the full unit group of the adele ring of $K$ (a monoid homomorphism from the top subgroup of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$) subject to three conditions — `hξc`, continuity of $z\mapsto\xi_K(z)$ as a map into $\mathbb{C}$; `hξt`, triviality of $\xi_K$ on the image of $K^\times$ under the unit map of $K\to\mathbb{A}_K$; and `hξu`, $|\xi_K(z)|=1$ for every $z$ — an ideal $N$ of $\mathcal{O}_K$ such that every prime $v$ with $v\mid N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place $w$ of $K$ a finite list of finite-dimensional representations of the row-isometry subgroup at $w$.
--
--   The modulus character $\alpha_m$ is the homomorphism $(\mathbb{A}_K)^\times\to\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ by passing from $\mathbb{R}_{\ge 0}$ to $\mathbb{R}$ and then to units; the adele ring carries its Borel $\sigma$-algebra. The hypothesis `hαm` asserts that $\alpha_m(x)>0$ for all $x$. For a character $\chi$ and $s\in\mathbb{C}$, `etaFst` $\chi$ at $s$ is $\chi\cdot\alpha_m^{\,s+1/2}$ and `etaSnd` $\chi$ at $s$ is $\chi\cdot\alpha_m^{-(s+1/2)}$, the powers being formed by complex exponentiation of the positive real $\alpha_m(x)$. A function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_K)$ is an induced section for a pair $(\chi_1,\chi_2)$ when $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for every upper-triangular $b$ in the adelic Borel subgroup and every $g$.
--
--   Continuous-block data. A countable index type $\iota_E$ is given, together with characters $\mu_e,\nu_e$ of $(\mathbb{A}_K)^\times$ ($e\in\iota_E$) satisfying: `_hμ`, `_hν`, all values of modulus $1$; `_hμic`, `_hνic`, triviality on principal ideles coming from $K^\times$; `_hμc`, `_hνc`, continuity; `_hμν`, $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $e$ and $z$; and `_hdist`, for $e\ne e'$ there is $z$ in the norm-one ideles (the kernel of the distributive Haar character) with $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$. For each $e$ a natural number $n_E(e)$ and functions $\varphi_{e,j}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, $j<n_E(e)$, are given, with the following groups of hypotheses: `_hφE`, each $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair $(\mu_e\alpha_m^{s+1/2},\nu_e\alpha_m^{-(s+1/2)})$; `_hφEK`, archimedean $K$-finiteness (at each infinite place the right translates under the archimedean row-isometry subgroup span a finite-dimensional space); `_hφEf`, smoothness as a vector for the finite adelic subgroup (the kernel of the archimedean projection); `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for each fixed $g$; `_hφEKu`, a uniform version of $K$-finiteness, namely for each $e,j$ and each infinite place $w$ a finite-dimensional subspace $W$ of functions on the row-isometry subgroup at $w$ containing all the functions $k\mapsto\varphi_{e,j}(s,gk)$; `_hφEflat`, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k$ in the adelic maximal compact subgroup (finite part integral, archimedean parts row isometries); `_hφElev`, right invariance under the intersection of the principal level at $N$ with the finite adelic subgroup; `_hφEty`, $\varphi_{e,j}(s,\cdot)$ lies in the archimedean cut submodule of $\mathrm{tys}_K$; `_hφEon`, orthonormality at $s=0$ over the maximal compact subgroup for its Haar measure, $\int \varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,dk=\delta_{ij}$; and `_hφEspan`, completeness on the imaginary axis: for $t\in\mathbb{R}$, every $\varphi_0$ which is an induced section for the pair at $s=it$, is continuous, archimedean $K$-finite, right invariant under the principal level at $N$ intersected with the finite adelic subgroup, and lies in the archimedean cut submodule of $\mathrm{tys}_K$, belongs to the complex span of the $\varphi_{e,j}(it,\cdot)$, $j<n_E(e)$.
--
--   Axis-continuation package for the blocks. Sets $O_{e,j}\subseteq\mathbb{C}$ and functions $E_{e,j},N_{e,j}$ of $(s,g)$ are given, with the hypothesis `_hEE` (nine clauses for each $e,j$): $O_{e,j}$ is open and preconnected and contains both the line $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb{A}_K)$ jointly; and for $\operatorname{Re}s>1/2$ one has the two-term Eisenstein expansion $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}(s,\,w\,u(\xi)\,g)$, with $w$ the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $u(\xi)=\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$, and the Weyl intertwining identity $N_{e,j}(s,g)=\int_{\mathbb{A}_K}\varphi_{e,j}(s,\,w^{-1}u(x)g)\,dx$ for the additive Haar measure on $\mathbb{A}_K$.
--
--   Test function. A function $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ is given, continuous (`_hf`) and of compact support (`_hfc`), and assumed factorizable (a product of a compactly supported smooth archimedean factor and a compactly supported locally constant finite factor), bi-invariant under the intersection of the principal level at $N$ with the finite adelic subgroup, and archimedean bi-finite for $\mathrm{tys}_K$ (that is, $x\mapsto f(x^{-1})$ lies in the archimedean cut submodule and $f$ lies in the archimedean dual cut submodule).
--
--   Finite Paley–Wiener datum. A finite index type $\iota_P$ is given with characters $\mu_{P,e},\nu_{P,e}$ satisfying `_hμ`, `_hν` (modulus one), `_hμic`, `_hνic` (trivial on principal ideles), `_hμc` and `_hνc` (continuity), and `_hμν`: $\mu_{P,e}(z)\nu_{P,e}(z)=\xi_K(z)$ for $z$ in the subgroup $Z$ of the carrier-pin package `productionPinsOf` formed from the canonical truncation domain for $\alpha,\beta$, the levels $M\mapsto$ principal level at $M$ intersected with the finite adelic subgroup, the Hecke generators, and the adelic box, this subgroup being the whole unit group. An exact swap $r_P:\iota_P\to\iota_P$ is given with `_hr`: $\mu_{P,r_Pe}=\nu_{P,e}$ and $\nu_{P,r_Pe}=\mu_{P,e}$; and `_hdist` separates distinct indices by norm-one ideles as above. Families $\varphi_{f,e},\psi_{f,e}$ of functions of $(s,g)$ are given with: `_hφf`, `_hψf`, both induced sections for the pair $(\mu_{P,e}\alpha_m^{s+1/2},\nu_{P,e}\alpha_m^{-(s+1/2)})$; `_hφjc`, `_hψjc`, joint continuity; `_hφhol`, `_hψhol`, holomorphy in $s$; `_hψK`, `_hψsm`, `_hψKu`, archimedean $K$-finiteness, smoothness for the finite adelic subgroup, and uniform archimedean $K$-finiteness for $\psi_{f,e}$; and the vertical decay hypotheses `_hφdec`, `_hψdec`: for each $e$, each $n\in\mathbb{N}$, each $\sigma_0\in\mathbb{R}$ and each compact $C$ there is an integrable, bounded-above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\varphi_{f,e}(\sigma'+it,g)\|\le m(t)$ (respectively for $\psi_{f,e}$) whenever $|\sigma'|\le\sigma_0$, $t\in\mathbb{R}$ and $g\in C$. Sets $O_{\psi,i}$ and functions $E_{\psi,i},N_{\psi,i}$ satisfy `_hEψ`, the same nine-clause axis-continuation package as `_hEE`, with $\psi_{f,i}$ in place of $\varphi_{e,j}$.
--
--   Matching and growth. Maps $e_m:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ are given with `_hem`: $\mu_{P,i}=\mu_{e_m(i)}\cdot\|\cdot\|^{\,i\tau_i}$ and $\nu_{P,i}=\nu_{e_m(i)}\cdot(\|\cdot\|^{\,i\tau_i})^{-1}$, where $\|\cdot\|^{\,i t}$ denotes the norm-power character $x\mapsto(\text{idele norm of }x)^{It}$. Finally `_hNψ` and `_hNE` give polynomial growth on the imaginary axis over the maximal compact: for each $i$ (respectively each $e,j$) there are $A\in\mathbb{R}$ and $n\in\mathbb{N}$ with $\|N_{\psi,i}(it,k)\|\le A(1+|t|)^n$ (respectively $\|N_{e,j}(it,k)\|\le A(1+|t|)^n$) for all $t\in\mathbb{R}$ and all $k$ in the adelic maximal compact subgroup. An index $i\in\iota_P$ and a real number $t$ are fixed.
--
--   Conclusion. Write $e=e_m(i)$, $e'=e_m(r_Pi)$, $s=i(t+\tau_i)$, $s'=i(-t+\tau_{r_Pi})$, and let $v$ be the real number obtained as the additive Haar measure of the adelic box, viewed in $\mathbb{C}$. Then both of the following hold.
--
--   First, for every $j<n_E(e)$ there are coefficients $d_l\in\mathbb{C}$, $l<n_E(e')$, such that for every $k$ in the adelic maximal compact subgroup
--   $$v^{-1}N_{e,j}(s,k)=\sum_{l<n_E(e')}d_l\,\varphi_{e',l}(s',k).$$
--
--   Second, for every $l<n_E(e')$ there are coefficients $d'_j\in\mathbb{C}$, $j<n_E(e)$, such that for every $k$ in the adelic maximal compact subgroup
--   $$\varphi_{e',l}(s',k)=\sum_{j<n_E(e)}d'_j\,\bigl(v^{-1}N_{e,j}(s,k)\bigr).$$
--
--   Thus, restricted to the maximal compact subgroup, the normalised Weyl-intertwining continuations $v^{-1}N_{e,j}(s,\cdot)$ and the induced family $\varphi_{e',l}(s',\cdot)$ span one another.
--
--   This is the span-transport step in the comparison of the continuous-spectrum blocks at $i$ and at its swap $r_Pi$: on the maximal compact subgroup the normalised constant-term (Weyl intertwining) continuation of the orthonormal block at $e_m(i)$ and the induced family at $e_m(r_Pi)$ generate the same finite-dimensional space, the two shifted imaginary-axis points being matched by the character identities `_hem` and the exact swap `_hr`. It feeds the identities [`AutomorphicForm.integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched`](thm.html#AutomorphicForm.integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched) and [`AutomorphicForm.sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched`](thm.html#AutomorphicForm.sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched), and rests on [`AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family`](thm.html#AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_inv_vol_mul_axis_continuation_weylIntertwining_eq_sum_and_exists_forall_eq_sum_of_paleyWiener_matched_swap.lean

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

theorem AutomorphicForm.exists_forall_inv_vol_mul_axis_continuation_weylIntertwining_eq_sum_and_exists_forall_eq_sum_of_paleyWiener_matched_swap
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
    (∀ j : Fin (nE (em i)), ∃ d : Fin (nE (em (rP i))) → ℂ, ∀ k : adelicMaximalCompact K,
        (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) =
          ∑ l : Fin (nE (em (rP i))), d l * φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∧
    (∀ l : Fin (nE (em (rP i))), ∃ d' : Fin (nE (em i)) → ℂ, ∀ k : adelicMaximalCompact K,
        φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) =
          ∑ j : Fin (nE (em i)), d' j * ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) := by sorry
