-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_setIntegral_tsum_integral_sum_rightConv_axis_continuation
-- name    : AutomorphicForm.exists_forall_setIntegral_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_setIntegral_tsum_integral_sum_rightConv_axis_continuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/fcf4deda-2ceb-5d17-b570-7f0ea614cb47
-- title:
--   Rectangle form of the GL₂ spectral kernel expansion
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}=\mathbb{A}_K$ its adele ring, and `AdelicGL2 (𝓞 K) K` denotes $\mathrm{GL}_2(\mathbb{A})$; the group $\mathrm{GL}_2(\mathbb{A})$ carries its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`, and $\mathbb{A}$ carries `adeleBorel` and the additive Haar measure `adelicAddHaar`.
--
--   *Slab, Siegel covering and central data.* Real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$ are fixed, together with a set $\Phi_K\subseteq\mathrm{GL}_2(\mathbb{A})$ on which no hypothesis is imposed, real numbers $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$, and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A})$. The hypothesis `hcovK` states that the union $\bigcup_{x\in T_K}\,(\cdot\,x)\bigl(\,\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}\bigr)$ of right translates of the centre-cut Siegel set — the set of $g$ whose finite part is integral, with $c_K\le$ the local height of the archimedean component at every infinite place, with $x$-window square $\le u_K^2$ at every infinite place, and with archimedean determinant norm in $[d_{1K},d_{2K}]$ at every infinite place — covers $\mathrm{GL}_2(\mathbb{A})$ modulo $\mathrm{GL}_2(K)$ on the left and the adelic centre on the right: for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}^\times$ with $\gamma g\,z\cdot 1$ in that union. Further, $\mathbb{A}^\times$ carries a measurable structure which is Borel for its topology, $\nu_{Z,K}$ is a Haar measure on $\mathbb{A}^\times$, and $\Omega_K\subseteq\mathbb{A}^\times$ is, by `hΩK`, a fundamental domain for the image of $K^\times$ in $\mathbb{A}^\times$ with respect to $\nu_{Z,K}$.
--
--   *Character, level and archimedean types.* $S_K$ is a finite set of finite places; $\xi_K$ is a homomorphism from the full subgroup $\top\le\mathbb{A}^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and of absolute value $1$ at every idele (`hξu`). $N$ is an ideal of $\mathcal{O}_K$ such that every finite place dividing $N$ lies in $S_K$ (`hN`), and $\mathrm{tys}_K$ is an archimedean type family, i.e. for each infinite place $w$ a number $\mathrm{card}(w)$ of representations of the row-isometry group of $K_w$. The character $\alpha_m:\mathbb{A}^\times\to\mathbb{R}^\times$ is the module character `distribHaarChar` of $\mathbb{A}$ pushed into $\mathbb{R}^\times$, and $h_{\alpha m}$ asserts that all its values are positive.
--
--   The pins used throughout are $\mathrm{pins}=$ `productionPinsOf` applied to the canonical truncation domain $\Phi_0=\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta$, to the level family $M\mapsto \mathrm{principalLevel}\,M\sqcap \mathrm{finiteAdelicGL2Subgroup}$, to the Hecke generators $v\mapsto \mathrm{heckeGen}\,v$ and to the adelic box; thus the measure is `adelicGLHaar`, the domain is $\Phi_0$, the central subgroup is $\top\le\mathbb{A}^\times$, and the adelic measure is the additive Haar measure conditioned on the box.
--
--   The assertion is: there exists $\kappa\in\mathbb{R}$ with $0<\kappa$ such that for all the following further data the displayed identity holds.
--
--   *Cuspidal system.* An index type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A})\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ`, subject to: `hb`, each $\mathrm{cls}\,i$ lies in $\mathrm{cuspClasses}$ for $(\mathrm{pins},\xi_K,N,S_K)$ — level $N$, vanishing $a_v,b_v$ for $v\in S_K$, non-zero isotypic cusp space — and $b_i$ lies in the isotypic cusp submodule of $\mathrm{cls}\,i$ (the $\mathbb{C}$-span of the continuous smooth cuspidal automorphic functions with central character $\xi_K$, right $U(N)$-invariant, Hecke eigen at $v\notin S_K$ with the prescribed eigenvalues and with the prescribed central eigenvalues) intersected with the archimedean cut submodule $\mathrm{archCutSubmodule}\,K\,\mathrm{tys}_K$; `hbn`, $\int_{\Phi_0} b_i\overline{b_i}=1$; `hbo`, $\int_{\Phi_0} b_i\overline{b_j}=0$ for $i\neq j$; `hbs`, for every cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the span of $b$ over that fibre is exactly the isotypic cusp submodule of $\pi$ intersected with the archimedean cut submodule; `hbc`, completeness: every $\varphi$ which is a smooth cuspidal automorphic function for $(\mathrm{pins},\xi_K)$, continuous, right invariant under $U(N)=\mathrm{principalLevel}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, in the archimedean cut submodule and orthogonal over $\Phi_0$ to every $b_i$, vanishes almost everywhere for Haar measure restricted to $\Phi_0$.
--
--   *Eisenstein data.* A countable type $\iota_E$, families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb{A}^\times,\mathbb{C}^\times)$ with hypotheses (summarised here) that each $\mu_e,\nu_e$ is unitary, trivial on $K^\times$, continuous, that $\mu_e\nu_e=\xi_K$, and that distinct indices are separated by a norm-one idele; natural numbers $n_E(e)$ and families $\varphi_{e,j}:\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A})\to\mathbb{C})$, $j\in\mathrm{Fin}(n_E(e))$, subject to the hypotheses (summarised here) that each $\varphi_{e,j}(s)$ is an induced section for the pair $\bigl(\mu_e\|\cdot\|^{s+1/2},\ \nu_e\|\cdot\|^{-(s+1/2)}\bigr)$ built from $\alpha_m$, is archimedean $K$-finite and $K_f$-smooth, is jointly continuous in $(s,g)$ and holomorphic in $s$ for each $g$, has right translates under the row-isometry group at each infinite place inside a fixed finite-dimensional space, satisfies $\varphi_{e,j}(s)(k)=\varphi_{e,j}(0)(k)$ on the adelic maximal compact, is right $U(N)$-invariant, lies in the archimedean cut submodule, has $\int_{\text{max.\ compact}}\varphi_{e,i}(0)\overline{\varphi_{e,j}(0)}=\delta_{ij}$, spans at $s=it$ all such sections for the pair $(\mu_e,\nu_e)$, and, by `_hpairs`, that every unitary idele-class pair $(\mu',\nu')$ with $\mu'\nu'=\xi_K$ admitting a non-zero such section at some $s=it$ agrees with some $(\mu_e,\nu_e)$ on norm-one ideles. Finally, sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_E(e,j),N_E(e,j):\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A})\to\mathbb{C})$ with `_hEE`: $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ both $s\mapsto E_E(e,j)(s)(g)$ and $s\mapsto N_E(e,j)(s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A})$; and for $\mathrm{Re}\,s>1/2$ one has $E_E(e,j)(s)(g)=\varphi_{e,j}(s)(g)+\sum'_{\xi\in K}\varphi_{e,j}(s)\bigl(w\,u(\xi)\,g\bigr)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix, and $N_E(e,j)(s)(g)$ is the Weyl intertwining integral $\int_{\mathbb{A}}\varphi_{e,j}(s)(w^{-1}u(x)g)\,dx$.
--
--   *Test function and rectangle.* A function $f:\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ which is continuous, compactly supported, factorizable (an archimedean factor that is a compactly supported smooth function of the matrix entries times a locally constant compactly supported factor on the finite part), bi-invariant under $\mathrm{principalLevel}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, and archimedean bi-finite for $\mathrm{tys}_K$ (that is, $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ lies in the archimedean dual cut submodule); a compact set $C\subseteq\mathrm{GL}_2(\mathbb{A})$ and measurable subsets $A,B\subseteq C$.
--
--   *Conclusion.* Write $\mathrm{vol}_Z=\nu_{Z,K}\bigl(\Omega_K\cap\{z\mid \mathrm{ideleNorm}\,\det(z\cdot 1)\in[\alpha,\beta]\}\bigr)$ and $\mathrm{vol}_{\Phi_0}=\mathrm{adelicGLHaar}(\Phi_0)$, both as real numbers cast to $\mathbb{C}$. Then, with both integrals taken over $A\times B$ for the product of the Haar measure restricted to $\Phi_0$ with itself,
--   $$\int_{A\times B}\Bigl[\ \sum^{f}_{q\in \mathrm{GL}_2(K)/Z}\ \int_{\mathbb{A}^\times}\xi_K(z)\,f\bigl(p_1^{-1}\,\gamma_q\,(z\cdot 1)\,p_2\bigr)\,d\nu_{Z,K}(z)\ -\ \mathrm{vol}_Z\sum_{i\in\iota}\mathrm{convOp}(f)(b_i)(p_1)\,\overline{b_i(p_2)}$$
--   $$-\ \frac{\mathrm{vol}_Z}{\mathrm{vol}_{\Phi_0}}\sum^{f}_{\chi}\Bigl(\int f\,\chi\!\circ\!\det\Bigr)\,\chi(\det p_1)\,\chi^{-1}(\det p_2)\ \Bigr]\,d(p_1,p_2)$$
--   $$=\ \kappa\int_{A\times B}\sum_{e\in\iota_E}\int_{\mathbb{R}}\sum_{i,j}\Bigl(\int_{\text{max.\ compact}}\mathrm{rightConv}\bigl(\varphi_{e,j}(it)\bigr)(f)(k)\,\overline{\varphi_{e,i}(it)(k)}\,dk\Bigr)\,E_E(e,i)(it)(p_1)\,\overline{E_E(e,j)(it)(p_2)}\,dt\ d(p_1,p_2).$$
--   Here the first sum is the finite sum (`finsum`) over the quotient of $\mathrm{GL}_2(K)$ by its centre, $\gamma_q$ being the image in $\mathrm{GL}_2(\mathbb{A})$ of the chosen representative `q.out`; $z\cdot 1$ is the central scalar matrix attached to $z$; $\mathrm{convOp}(f)(u)=\mathrm{rightConv}(u)(f)$, so $\mathrm{convOp}(f)(b_i)(x)=\int b_i(xy)f(y)\,dy$ for Haar measure on $\mathrm{GL}_2(\mathbb{A})$, and the sum over $i$ is a `tsum`; the third sum is the finite sum over those characters $\chi:\mathbb{A}^\times\to\mathbb{C}^\times$ whose square equals $\xi_K$ on $\top$, which are trivial on the image of $K^\times$ and continuous, with $\chi\circ\det$ written `chiDet`; the sum over $e$ on the right is a `tsum`, the inner integral in $t$ is over $\mathbb{R}$ with $s=it$, the double sum runs over $i,j\in\mathrm{Fin}(n_E(e))$, and the coefficient integral is taken against the Haar measure `maximalCompactHaar` of the adelic maximal compact subgroup.
--
--   This is the $L^2$ spectral expansion of the automorphic kernel for $\mathrm{GL}_2$ over a number field in 'rectangle' form: the difference between the geometric (folded) kernel and its cuspidal and residual parts, integrated over a measurable rectangle $A\times B$ inside a compact set against Haar measure restricted to the canonical truncation domain, equals a fixed positive multiple of the corresponding integral of the continuous (Eisenstein) kernel written through the axis continuations $E_E$. It is the form from which the almost-everywhere identity for the kernels is obtained, by uniqueness of locally integrable kernels from their integrals over rectangles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_setIntegral_tsum_integral_sum_rightConv_axis_continuation.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_setIntegral_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_setIntegral_tsum_integral_sum_rightConv_axis_continuation
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
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
    ∃ κ : ℝ, 0 < κ ∧
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
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
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
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
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
    ∀ A ⊆ C, MeasurableSet A → ∀ B ⊆ C, MeasurableSet B →
      ∫ p in A ×ˢ B,
        ((∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * p.2)) ∂νZK) -
        (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) p.1 * conj (b i p.2)) -
        (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ p.1 * chiDet (𝓞 K) K χ⁻¹ p.2))) ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) =
      (κ : ℂ) * ∫ p in A ×ˢ B,
        (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) p.1 * conj (EE e j ((t : ℂ) * Complex.I) p.2))) ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) := by sorry
