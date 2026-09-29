-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched
-- name    : AutomorphicForm.integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/4751941b-791b-543d-bab5-da7f40f7c58d
-- title:
--   Adjoint transport of the axis intertwining operator
-- statement:
--   Throughout, $K$ is a number field, $\alpha,\beta$ are reals with $0<\alpha$ and $\alpha<\beta$, $SK$ is a finite set of finite places of $K$, and $\xi_K$ is a homomorphism from the full idele unit group (taken as the top subgroup of $(\mathbb{A}_K)^\times$) to $\mathbb{C}^\times$, subject to: `hξc`, continuity of $z\mapsto \xi_K(z)$; `hξt`, triviality of $\xi_K$ on the image of $K^\times$; and `hξu`, $|\xi_K(z)|=1$ for all $z$. Further, $N$ is an ideal of $\mathcal{O}_K$ with `hN`: every finite place $v$ whose prime ideal divides $N$ belongs to $SK$; and $tysK$ is an archimedean type family for $K$, i.e. a number $\mathrm{card}(w)$ of types at each infinite place $w$ together with, for each index, a finite-dimensional representation of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$.
--
--   The statement introduces $\alpha_m$, the $\mathbb{R}^\times$-valued homomorphism on $(\mathbb{A}_K)^\times$ obtained from the module character `distribHaarChar` of the adele ring composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, the adeles carrying the Borel $\sigma$-algebra, and assumes `hαm`: $\alpha_m(x)>0$ for every $x$. For a character $\chi$ and $s\in\mathbb{C}$, `etaFst` $\chi$ is $\chi\cdot\alpha_m^{\,s+1/2}$ and `etaSnd` $\chi$ is $\chi\cdot\alpha_m^{-(s+1/2)}$, and `IsInducedSection` for a pair $(\chi_1,\chi_2)$ means $\varphi(bg)=\chi_1(b_{00})\chi_2(b_{11})\varphi(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (lower-left entry zero).
--
--   The Eisenstein side. $\iota E$ is a countable index type, and $\mu,\nu:\iota E\to\mathrm{Hom}((\mathbb{A}_K)^\times,\mathbb{C}^\times)$ satisfy: unitarity of each $\mu(e)$, $\nu(e)$ (absolute value $1$ everywhere); triviality on the image of $K^\times$; continuity; `_hμν`, $\mu(e)(z)\nu(e)(z)=\xi_K(z)$ for all $z$; and `_hdist`, for $e\neq e'$ some norm-one idele (an element of the kernel of `distribHaarChar`) separates either the $\mu$'s or the $\nu$'s. For each $e$ there are $nE(e)$ functions $\varphi_{e,j}(s,\cdot)$ on $\mathrm{GL}_2(\mathbb{A}_K)$, subject to the following hypotheses: `_hφE`, each $\varphi_{e,j}(s,\cdot)$ is an induced section for $(\mathrm{etaFst}\,\mu(e)\,s,\ \mathrm{etaSnd}\,\nu(e)\,s)$; `_hφEK`, archimedean $K$-finiteness (at each infinite place the right translates under the archimedean row-isometry subgroup span a finite-dimensional space); `_hφEf`, smoothness as a vector for right translation by the finite adelic subgroup (the kernel of the archimedean projection); `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for each fixed $g$; `_hφEKu`, a finite-dimensional space $W$ of functions on the archimedean row-isometry subgroup at each infinite place containing all right-translate functions $k\mapsto\varphi_{e,j}(s,gk)$, uniformly in $s$ and $g$; `_hφEflat`, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k$ in the adelic maximal compact subgroup (integral finite part, row-isometric archimedean components); `_hφElev`, right invariance under $\mathrm{principalLevel}(N)\sqcap$ the finite adelic subgroup; `_hφEty`, membership in the archimedean cut submodule attached to $tysK$; `_hφEon`, orthonormality on the maximal compact subgroup, $\int_{\mathbf K}\varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,dk=\delta_{ij}$ for the Haar measure `maximalCompactHaar`; and `_hφEspan`, that for every real $t$ any $\varphi_0$ which is an induced section at $s=it$ for $(\mathrm{etaFst}\,\mu(e),\mathrm{etaSnd}\,\nu(e))$, continuous, archimedean $K$-finite, invariant under the same level subgroup and in the archimedean cut submodule, lies in the complex span of the $\varphi_{e,j}(it,\cdot)$.
--
--   Continuation data on the Eisenstein side: sets $OE(e,j)\subseteq\mathbb{C}$ and functions $EE(e,j),NE(e,j)$, constrained by `_hEE` (nine clauses): $OE(e,j)$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ both $s\mapsto EE(e,j,s,g)$ and $s\mapsto NE(e,j,s,g)$ are analytic on a neighbourhood of each point of $OE(e,j)$; both are continuous in $(s,g)$ on $OE(e,j)\times\mathrm{univ}$; for $\mathrm{Re}\,s>1/2$, $EE(e,j,s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}(s,\,w\,u(\xi)\,g)$ with $w$ the adelic Weyl element and $u(\xi)$ the upper unipotent with entry $\xi$; and for $\mathrm{Re}\,s>1/2$, $NE(e,j,s,g)$ is the Weyl intertwining integral $\int \varphi_{e,j}(s,\,w^{-1}u(x)g)\,dx$ against the additive adelic Haar measure.
--
--   A test function $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ is assumed continuous with compact support, factorizable (a product of an archimedean factor given by a smooth compactly supported function of the matrix entries and a locally constant compactly supported finite factor), bi-invariant under $\mathrm{principalLevel}(N)\sqcap$ the finite adelic subgroup, and archimedean bi-finite for $tysK$ (that is, $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ lies in the archimedean dual cut submodule).
--
--   The Paley–Wiener side. $\iota P$ is a finite index type with characters $\mu_P,\nu_P:\iota P\to\mathrm{Hom}((\mathbb{A}_K)^\times,\mathbb{C}^\times)$, assumed unitary, trivial on $K^\times$, and continuous (for $\mu_P$ by `_hμc`, for $\nu_P$ by `_hνc`), with `_hμν`: $\mu_P(e)(z)\nu_P(e)(z)=\xi_K(z)$ for every $z$ in the central subgroup $Z$ of the carrier pins produced by `productionPinsOf` from the canonical truncation domain for $(\alpha,\beta)$, the level assignment $M\mapsto \mathrm{principalLevel}(M)\sqcap$ finite adelic subgroup, the Hecke generators and the adelic box (this subgroup being the top subgroup, so the condition holds for all ideles). There is a swap map $rP:\iota P\to\iota P$ with `_hr`: $\mu_P(rP\,e)=\nu_P(e)$ and $\nu_P(rP\,e)=\mu_P(e)$, and `_hdist`: distinct indices are separated by a norm-one idele on $\mu_P$ or on $\nu_P$. Two families $\varphi f,\psi f$ of sections are given with: `_hφf`, `_hψf`, each $\varphi f(e,s,\cdot)$ and $\psi f(e,s,\cdot)$ an induced section for $(\mathrm{etaFst}\,\mu_P(e)\,s,\ \mathrm{etaSnd}\,\nu_P(e)\,s)$; joint continuity in $(s,g)$ and holomorphy in $s$ for both; for $\psi f$ additionally archimedean $K$-finiteness, smoothness under the finite adelic subgroup, and a uniform finite-dimensional space of archimedean right translates at each infinite place; and vertical decay hypotheses `_hφdec`, `_hψdec`: for each index, each $n\in\mathbb{N}$, each $\sigma_0\in\mathbb{R}$ and each compact $C$, an integrable, bounded-above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\varphi f(e,\sigma'+it,g)\|\le m(t)$, respectively the same for $\psi f$, for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. Continuation data $O\psi,E\psi,N\psi$ for $\psi f$ satisfy `_hEψ`, the same nine clauses as `_hEE`, with $\psi f(i,s,\cdot)$ in place of $\varphi_{e,j}(s,\cdot)$.
--
--   The two sides are matched by $em:\iota P\to\iota E$ and $\tau:\iota P\to\mathbb{R}$ with `_hem`: $\mu_P(i)=\mu(em\,i)\cdot\|\cdot\|^{\,i\tau(i)}$ and $\nu_P(i)=\nu(em\,i)\cdot(\|\cdot\|^{\,i\tau(i)})^{-1}$, where $\|\cdot\|^{\,i\tau}$ denotes `normPowChar`, $x\mapsto (\text{idele norm of }x)^{\mathrm{I}\tau}$. Finally, polynomial bounds on the imaginary axis are assumed: `_hNψ`, for each $i$ there are $A\in\mathbb{R}$ and $n\in\mathbb{N}$ with $\|N\psi(i,it,k)\|\le A(1+|t|)^n$ for all real $t$ and all $k$ in the adelic maximal compact subgroup; and `_hNE`, the same for each $NE(e,j)$.
--
--   Conclusion. Fix $i\in\iota P$, $t\in\mathbb{R}$ and $k'<nE(em\,i)$, write $v=(\text{additive adelic Haar measure of the adelic box})$ viewed as a complex number, and let $\langle a,b\rangle=\int_{\mathbf K}a(k)\overline{b(k)}\,dk$ denote integration against `maximalCompactHaar` over the adelic maximal compact subgroup. Then two assertions hold. First,
--   $$\Big\langle \psi f(i,it,\cdot),\ \varphi_{em\,i,\,k'}\big(i(t+\tau(i)),\cdot\big)\Big\rangle=\Big\langle v^{-1}N\psi(i,it,\cdot),\ v^{-1}NE\big(em\,i,k',i(t+\tau(i)),\cdot\big)\Big\rangle.$$
--   Second, for every $l<nE(em(rP\,i))$,
--   $$\Big\langle \psi f(i,it,\cdot),\ v^{-1}NE\big(em(rP\,i),l,\,i(-t+\tau(rP\,i)),\cdot\big)\Big\rangle=\Big\langle v^{-1}N\psi(i,it,\cdot),\ \varphi_{em(rP\,i),\,l}\big(i(-t+\tau(rP\,i)),\cdot\big)\Big\rangle,$$
--   all arguments of the sections being written in the form $(\text{real})\cdot \mathrm{I}$ as indicated.
--
--   On the unitary axis the normalised Weyl intertwining operator $v^{-1}N$ transports pairings over the adelic maximal compact subgroup: it acts as an isometry against the Paley–Wiener sections and can be moved across a pairing onto the partner family indexed by the swap $rP$. The result feeds the computation of the Eisenstein contribution, being used by [`AutomorphicForm.sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched`](thm.html#AutomorphicForm.sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched.lean

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

theorem AutomorphicForm.integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched
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
      (i : ιP) (t : ℝ) (k' : Fin (nE (em i))),
    (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
        conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
    (∀ l : Fin (nE (em (rP i))),
      ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
          conj (φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by sorry
