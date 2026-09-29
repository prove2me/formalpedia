-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram
-- name    : AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/1aae303d-f4cf-5853-a33d-24522f570db8
-- title:
--   Truncated twisted unipotent term along Hecke words via local zetas
-- statement:
--   **Data and standing hypotheses.** Let $K$ and $L$ be number fields with $L/K$ Galois, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and let $\Phi_L\subseteq \mathrm{GL}_2(\mathbb{A}_L)$ be a set (here $\mathrm{GL}_2(\mathbb{A}_L)$ denotes `AdelicGL2 (𝓞 L) L`, the general linear group of degree $2$ over the adele ring of $L$). Let $\nu_{Z_L}$ be a Haar measure on $(\mathbb{A}_L)^\times$ and $\Omega_L\subseteq(\mathbb{A}_L)^\times$ a set which, by `hΩL`, is a fundamental domain for the action of the image of $L^\times$ in $(\mathbb{A}_L)^\times$ with respect to $\nu_{Z_L}$. Let $D$ be an idele Galois descent datum for $L/K$: a homomorphism $\mathrm{Gal}(L/K)\to\mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ compatible with the action on $L$ and continuous in each $\tau$. Let $\sigma\in\mathrm{Gal}(L/K)$, with `hgen` asserting that every $\tau\in\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$. Let $S_L$ be a finite set of finite places of $L$ and $\xi_L\colon\top\le(\mathbb{A}_L)^\times\to\mathbb{C}^\times$ a character of the full unit group, subject to: `hSL`, every place $w$ of $L$ whose ramification index over its restriction to $K$ is $\neq 1$ belongs to $S_L$; `hξc`, the complex-valued function $z\mapsto\xi_L(z)$ is continuous; and `hξt`, $\xi_L$ is trivial on the image of $L^\times$.
--
--   Let $S$ be a finite set of finite places of $K$, let $\varphi_a\colon\mathrm{GL}_2(\mathbb{A}_{L,\infty})\to\mathbb{C}$, and for each finite place $v$ of $K$ let $\varphi_{S,v}\colon\mathrm{GL}_2(L\otimes_K K_v)\to\mathbb{C}$. Let $c,u,d_1,d_2$ be reals with $0<c$, let $T_c\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ be compact, and let $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ satisfy the three geometric hypotheses: `hΦ₀S`, $\Phi_0$ is contained in the union over $y\in T_c$ of the right translates by $y$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` (those $g$ whose finite part lies in the integral subgroup, whose archimedean components have local height $\ge c$ and window quantity `xWindowSq` $\le u^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_1,d_2]$); `hΦ₀s`, $\Phi_0$ lies in the shell where the idele norm of $\det g$ belongs to $[\alpha,\beta]$; and `hΦ₀`, $\Phi_0$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(L)$ on $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` restricted to that shell. Finally, for every finite place $v$ of $K$ let $\mu_{f,v}$ be an additive Haar measure on the completion $K_v$, the completions carrying their Borel structures.
--
--   **Hecke-word data.** The assertion is then made for every finite set $T$ of finite places of $K$ subject to the unramifiedness hypothesis that for each $v\in T$ no place $w$ of $L$ with restriction $v$ lies in $S_L$; every family $w_\bullet$ assigning to each place $v$ of $K$ an extension $w_v$ of $v$ to $L$; every map $w'$ from places of $K$ to places of $L$ with $(w'_v)$ the ideal-theoretic translate $\sigma\cdot w_v$ for $v\in T$; every family $\varpi_\bullet$ with $\varpi_v$ in the valuation ring of $L_{w_v}$, irreducible for $v\in T$, together with the hypothesis `hϖs0` that the image of $\varpi_v$ in $L_{w_v}$ is nonzero for $v\in T$; every family of natural numbers $n_\bullet$ and every family $r_{T,v}\colon\mathrm{Fin}(n_v)\to\mathrm{GL}_2(L_{w_v})$ such that for $v\in T$ the tuple $r_{T,v}$ is a Hecke coset system for the integral subgroup $\mathrm{GL}_2(\mathcal{O}_{w_v})$ (the image of $\mathrm{GL}_2$ of the valuation ring) and the element $\mathrm{diag}(\varpi_v,1)$, i.e. each representative lies in the double coset, the cosets of the representatives cover the double coset modulo the integral subgroup, and distinct indices give distinct cosets; and every family $z_\bullet$ in $\mathrm{GL}_2(L_{w_v})$ with $z_v$ the central scalar matrix $\varpi_v\cdot 1$ for $v\in T$.
--
--   **Conclusion.** For such data there exist complex constants $\Lambda$, $\kappa_0$ and a third constant written `c` (shadowing the earlier real parameter of the same name), such that for every pair of families of natural numbers $k_\bullet,j_\bullet$ indexed by the places of $K$, every $\varphi\colon\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ and every $\varphi_f\colon\mathrm{GL}_2(\mathbb{A}_{L,f})\to\mathbb{C}$ forming a semi-local factorisation of $\varphi$ relative to the set $S\cup T$, with archimedean factor $\varphi_a$, finite factor $\varphi_f$, and local factors equal to $\varphi_{S,v}$ for $v\notin T$ and, for $v\in T$, to the Hecke-word indicator
--   $$x\longmapsto \sum_{\iota\colon \mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)} \mathbf 1_{\mathcal{I}_v}\Bigl(\bigl(\pi_v\bigl(\iota_{w_v}\bigl(\textstyle\prod_m r_{T,v}(\iota(m))\cdot z_v^{\,j_v}\bigr)\bigr)\bigr)^{-1}x\Bigr),$$
--   where the product is taken in the order of the indices, $\iota_{w_v}$ is the embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of $\mathrm{GL}_2(L_{w_v})$ into $\mathrm{GL}_2(\mathbb{A}_{L,f})$ at $w_v$, $\pi_v$ is `semiLocalComponent K L v` into $\mathrm{GL}_2(L\otimes_K K_v)$, and $\mathcal{I}_v$ is the semi-local integral set of those $g$ with $g$ and $g^{-1}$ having entries in the image of the tensor integers; being a semi-local factorisation means: $\varphi_a$ is an archimedean test factor (given by a smooth function of the matrix entries in the mixed space, with compact support), $\varphi_f$ is locally constant with compact support, each local factor at a place of $S\cup T$ is locally constant with compact support, $\varphi_f(h)=\prod_{v\in S\cup T}(\text{local factor at }v)(\pi_v h)$ whenever all semi-local components of $h$ outside $S\cup T$ are integral, $\varphi_f(h)=0$ as soon as some component outside $S\cup T$ is not integral, and $\varphi(g)=\varphi_a(\mathrm{glArch}\,g)\,\varphi_f(\mathrm{glFin}\,g)$ for all $g$ — there exists $R_0\in\mathbb{R}$ such that for all $R\ge R_0$ the following three statements hold.
--
--   Write, for $x\in\mathrm{GL}_2(\mathbb{A}_L)$ and $z\in(\mathbb{A}_L)^\times$,
--   $$F(x,z)\;=\;\sum_{\delta\in\mathcal{U}}\varphi\bigl(x^{-1}\,\delta\,{}^{\sigma}(z\cdot x)\bigr)\;-\;\mathbf 1_{\{\,\mathrm{ht}>e^{R}\,\}}(z\cdot x)\cdot \mathrm{CT}(z\cdot x),$$
--   made precise as follows. The first term is the finite-sum (`∑ᶠ`) over the set of $\delta\in\mathrm{GL}_2(L)$ for which there exists $\gamma$ in the unipotent cell of $\mathrm{GL}_2(K)$ — the $\gamma$ whose matrix is not of central type and has characteristic polynomial $(X-a)^2$ for some $a\in K$ — with the twisted norm class map [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) sending the $\sigma$-conjugacy class of $\delta$ to the conjugacy class of $\gamma$, of the values $\varphi\bigl(x^{-1}\cdot \mathrm{glob}(\delta)\cdot \mathrm{Act}_{D,\sigma}(\mathrm{scal}(z)\,x)\bigr)$, where $\mathrm{glob}$ is the embedding $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$, $\mathrm{scal}(z)$ is the central scalar matrix of $z$, and $\mathrm{Act}_{D,\sigma}$ is the automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ induced by $D.\mathrm{act}\,\sigma$. The second term is the indicator of the high set $\{g:\ \mathrm{adelicHeight}_L(g)>e^{R}\}$ applied, at the point $\mathrm{scal}(z)\,x$, to the constant term of the upper-triangular sum: namely to the function
--   $$g\longmapsto \int_{\mathbb{A}_L}\ \sum_{\delta\in\mathcal{B}}\varphi\bigl(x^{-1}\cdot\mathrm{glob}(\delta)\cdot\mathrm{Act}_{D,\sigma}(n(t)\,g)\bigr)\ d\nu(t),$$
--   where $n(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, $\mathcal{B}$ is the set of $\gamma\in\mathrm{GL}_2(L)$ with $\gamma_{10}=0$ and $\mathrm{N}_{L/K}(\gamma_{00}/\gamma_{11})=1$, the inner sum again being a `∑ᶠ`, and $\nu$ is the measure carried by `productionPinsOf L ΦL (fun M => levelOne ⊓ finiteAdelicGL2Subgroup) (fun w => heckeGen) (adelicBox L)`, i.e. the adelic additive Haar measure of $L$ conditioned on the adelic box of $L$, with the Borel structure of $\mathbb{A}_L$.
--
--   The three conjuncts are:
--
--   (i) for every $x\in\mathrm{GL}_2(\mathbb{A}_L)$ the function $z\mapsto \xi_L(z)\,F(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z_L}$;
--
--   (ii) the function $x\mapsto\int_{\Omega_L}\xi_L(z)\,F(x,z)\,d\nu_{Z_L}(z)$ is integrable on $\Phi_0$ with respect to `adelicGLHaar (Fin 2) (𝓞 L) L`;
--
--   (iii) with $Z_v(s)=$ [`LanglandsTunnell.TateLocal.localZeta`](def/LanglandsTunnell_TateLocalZeta.html#L125) $(\mu_{f,v})\bigl(\mathrm{TLF}_v\bigr)\,1\,s$, the Tate local zeta integral at the trivial character of the local factor $\mathrm{TLF}_v=$ [`twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v)`](def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L85) on $K_v$ (the local-trace pushforward to $K_v$ of the twisted unipotent orbital function attached to $\xi_L$, the place $w_v$ and the word data $n_v,r_{T,v},z_v,k_v,j_v$),
--   $$\int_{\Phi_0}\int_{\Omega_L}\xi_L(z)\,F(x,z)\,d\nu_{Z_L}(z)\,dx\;=\;\Lambda\Bigl(R\prod_{v\in T}Z_v(1)\;+\;c\sum_{p\in T}Z_p'(1)\prod_{v\in T,\ v\neq p}Z_v(1)\Bigr)\;+\;\kappa_0\prod_{v\in T}Z_v(1),$$
--   the products and sums being over the places of $T$ viewed as a type, and $Z_p'(1)$ the derivative in $s$ at $s=1$ of $s\mapsto Z_p(s)$. The constants $\Lambda,\kappa_0,c$ are chosen before the word exponents $k_\bullet,j_\bullet$, the test function $\varphi$ and the truncation parameter $R$, and hence are independent of them.
--
--   This is the global half of the evaluation of the unipotent-type contribution to the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$: the truncated kernel, folded against the central character $\xi_L$ and integrated over a fundamental domain, is an affine function of the truncation parameter $R$ whose coefficients are the product of Tate local zeta values at $s=1$ over the unramified Hecke places of $T$ and its logarithmic-derivative variants. It feeds the weighted-moment form of the same identity, where the local zeta values and derivatives are replaced by their explicit local evaluations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem
    AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)) [∀ v, (μf v).IsAddHaarMeasure] :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ Λ κ₀ c : ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        Λ * ((R : ℂ) * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i)
                (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1 +
            c * ∑ p : T, deriv (fun s : ℂ => LanglandsTunnell.TateLocal.localZeta (μf p)
                (twistedLocalFactor K L D σ ξL p (ws p) (ns p) (rTs p) (zs p) (ks p) (js p)) 1 s) 1 *
                ∏ i ∈ Finset.univ.erase p, LanglandsTunnell.TateLocal.localZeta (μf i)
                (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1) +
          κ₀ * ∏ i : T, LanglandsTunnell.TateLocal.localZeta (μf i)
                (twistedLocalFactor K L D σ ξL i (ws i) (ns i) (rTs i) (zs i) (ks i) (js i)) 1 1 := by sorry
