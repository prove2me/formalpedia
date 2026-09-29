-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_chiDet_mul_chiDet_inv
-- name    : AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_chiDet_mul_chiDet_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/f290bd6c-3a77-59f3-b64e-02af2d5cd119
-- title:
--   Residual block of the truncated GL₂ kernel: Eisenstein atoms
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal O_K$, adele ring $\mathbb A =$ `AdeleRing (𝓞 K) K`, and write $\mathrm{GL}_2(\mathbb A)$ for `AdelicGL2 (𝓞 K) K`.
--
--   *Slab and Siegel covering data.* Real numbers $\alpha<\beta$ with $0<\alpha$; a set $\Phi_K \subseteq \mathrm{GL}_2(\mathbb A)$; real numbers $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$; and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb A)$ such that `hcovK` holds: the union $\bigcup_{x\in T_K}(\cdot\,x)''\,\mathrm{centreCutSiegelSet}(K,c_K,u_K,d_{1K},d_{2K})$ covers $\mathrm{GL}_2(\mathbb A)$ modulo the centre, i.e. for every $g$ there are $\gamma\in \mathrm{GL}_2(K)$ and an idele class representative $z\in\mathbb A^\times$ with `globalPoints` $\gamma\cdot g\cdot$ `centralScalar` $z$ in that union. Here `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ satisfies `localHeight` $\ge c$ and `xWindowSq` $\le u^2$, and for which `archDetNorm` $w\,g\in[d_1,d_2]$ for every $w$.
--
--   *Central data.* A measurable space and Borel space structure on $\mathbb A^\times$, a Haar measure $\nu_{Z K}$ on $\mathbb A^\times$, and a set $\Omega_K$ which by `hΩK` is a fundamental domain for the action of the image of $K^\times$ in $\mathbb A^\times$ (the range of `Units.map (algebraMap K (AdeleRing (𝓞 K) K))`) with respect to $\nu_{ZK}$.
--
--   *Character, level, types, test factors.* A finite set $S_K$ of height one primes of $\mathcal O_K$; a homomorphism $\xi_K$ from the full subgroup $\top\le\mathbb A^\times$ to $\mathbb C^\times$ whose associated function $z\mapsto \xi_K(z)$ is continuous (`hξc`) and trivial on the principal ideles (`hξt`); an ideal $N\subseteq\mathcal O_K$ such that every $v$ with $v\mid N$ lies in $S_K$ (`hN`); an archimedean type family $\mathrm{tys}_K$ (for each infinite place a finite list of representation types of the relevant isometry subgroup); a function $f_{aK}$ on $\mathrm{GL}_2$ of the infinite adeles; and for each finite place $v$ a function $f_{SK,v}$ on $\mathrm{GL}_2(K_v)$.
--
--   *Table space.* A compact set $X$ of functions $v\mapsto (x_v^{(1)},x_v^{(2)})\in\mathbb C\times\mathbb C$ on the height one primes such that (`hX`) $X$ contains every table $x$ with $x_v=0$ for $v\in S_K$ and, for $v\notin S_K$: $x_v^{(2)} = \mathrm{cNorm}(v)\,\xi_K(\det \mathrm{heckeGen}(v))$, where $\mathrm{cNorm}(v)$ is the absolute norm of $v$ viewed in $\mathbb C$; $\|x_v^{(1)}\|\le (\mathrm{absNorm}\,v+1)\sqrt{\|\xi_K(\det \mathrm{heckeGen}(v))\|}$; and $\overline{x_v^{(1)}} = \bigl(\overline{x_v^{(2)}}/\|x_v^{(2)}\|\bigr)\,x_v^{(1)}$.
--
--   **Conclusion.** There exist a sequence of tables $\mathrm{tabs}:\mathbb N\to(\text{primes}\to\mathbb C\times\mathbb C)$, a proof $\mathrm{htabs}$ that $\mathrm{tabs}\,n\in X$ for all $n$, and coefficients $c:\mathbb N\to\mathbb C$, such that three assertions hold.
--
--   (i) The family $n\mapsto \|c_n\|$ is summable.
--
--   (ii) For every $n$ with $c_n\ne 0$ there are a nonzero ideal $M$ of $\mathcal O_K$ and characters $\chi_1,\chi_2:\mathbb A^\times\to\mathbb C^\times$ such that $z\mapsto\chi_1(z)$ and $z\mapsto\chi_2(z)$ are continuous, both $\chi_1$ and $\chi_2$ are trivial on the principal ideles, both satisfy [`NumberField.TateGlobal.IsUnramifiedCharAt`](def/NumberField_TateGlobalZeta.html#L59) at every $v\notin S_K$ (the local component of the character is trivial on the units $t$ of $K_v$ with $t$ and $t^{-1}$ integral), and for every $v\notin S_K$ the table entry $\mathrm{tabs}\,n\,v$ equals the pair $(a_v,b_v)$ of the Eisenstein eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), that is $a_v = \chi_1(\varpi_v)+\chi_2(\varpi_v)$ and $b_v=\chi_1(\varpi_v)\chi_2(\varpi_v)$, where $\varpi_v$ is the uniformizer idele at $v$.
--
--   (iii) For every finite set $T$ of height one primes disjoint from $S_K$ with $2\le \#T$; every family $\varpi$ with $\varpi_v$ in the valuation ring of $K_v$, irreducible for $v\in T$ and with nonzero image in $K_v$ for $v\in T$; every $n_{Ks}:\text{primes}\to\mathbb N$ and every family $r_{Ks,v}:\mathrm{Fin}(n_{Ks}(v))\to \mathrm{GL}_2(K_v)$ such that for each $v\in T$ the family $r_{Ks,v}$ is a Hecke coset system for the subgroup $\mathrm{integralSubgroup}(\mathcal O_v,K_v)$ and the element $\mathrm{diagPi}(\varpi_v)$ (each representative lies in the double coset, the representatives cover it modulo the subgroup on the right, and their classes are distinct); every family $z_{Ks}$ with $z_{Ks,v}$ the scalar matrix $\varpi_v\cdot 1$ for $v\in T$; every pair of exponent functions $k,j$; every continuous, compactly supported $f:\mathrm{GL}_2(\mathbb A)\to\mathbb C$ and every $f\!f$ on $\mathrm{GL}_2$ of the finite adeles such that `IsUnitFactorization K (SK ∪ T) f faK ff` holds for the local data given at $v\in T$ by $x\mapsto \sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_{Ks}(v))}\mathbf 1_{\mathrm{localIntegralSet}(K,v)}\bigl((\prod_m r_{Ks,v}(\iota\,m)\cdot z_{Ks,v}^{\,j_v})^{-1}x\bigr)$ (ordered product over $m$) and at $v\notin T$ by $f_{SK,v}$ — that is, $f_{aK}$ is a smooth compactly supported archimedean factor, $f\!f$ is locally constant with compact support, the local factors at the places of $S_K\cup T$ are locally constant with compact support, $f\!f(h)$ is the product of the local factors over $S_K\cup T$ whenever all components of $h$ outside $S_K\cup T$ are integral and vanishes otherwise, and $f(g)=f_{aK}(\mathrm{glArch}\,g)\,f\!f(\mathrm{glFin}\,g)$ — and such that $f$ is bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and satisfies `IsArchBiFinite K tysK f` (the function $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule of the type family and $f$ lies in the dual cut submodule); and finally for every continuous $g:X\to\mathbb C$ with $g(x)=\prod_{v\in T}(x_v^{(1)})^{k_v}\,\bigl(\mathrm{cNorm}(v)^{-1}x_v^{(2)}\bigr)^{j_v}$: the following two statements hold.
--
--   Write, for $x\in \mathrm{GL}_2(\mathbb A)$,
--   $$\varphi_x(y') = \frac{\nu_{ZK}\bigl(\Omega_K\cap\{z:\mathrm{ideleNorm}_K(\det \mathrm{centralScalar}(z))\in[\alpha,\beta]\}\bigr)}{\mathrm{adelicGLHaar}\bigl(\mathrm{canonicalTruncationDomain}(K,\alpha,\beta)\bigr)}\ \sum_{\chi}\Bigl(\int f(g)\,\chi(\det g)\,d\,\mathrm{adelicGLHaar}\Bigr)\chi(\det x)\,\chi^{-1}(\det y'),$$
--   where the measures are taken in real form and cast to $\mathbb C$, and the sum is the `∑ᶠ` over those characters $\chi:\mathbb A^\times\to\mathbb C^\times$ satisfying `SquaresToXi (𝓞 K) K ⊤ ξK χ` (that is $\chi(z)^2=\xi_K(z)$ for all $z$), trivial on the principal ideles, and with $z\mapsto\chi(z)$ continuous. Let $\lambda^{T}$ denote [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) taken with the Borel measurable structure on $\mathbb A$ and the measure from `productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, whose relevant fields are the Borel structure `adeleBorel` and the conditioning of `adelicAddHaar` on `adelicBox K`, with unipotent family $t\mapsto \mathrm{unipotentGL2}(t)$, height function [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158) and threshold $\exp R$; thus $\lambda^{\exp R}\varphi_x(x) = \varphi_x(x) - \mathbf 1_{\{\mathrm{adelicHeight} > \exp R\}}(x)\cdot(\mathrm{constantTerm}\,\varphi_x)(x)$, the constant term being the integral of the unipotent integrand against that conditioned measure. The conclusion of the parenthetical data above is then:
--
--   $\bullet$ for every $R\in\mathbb R$, the function $x\mapsto \lambda^{\exp R}\varphi_x(x)$ is integrable on `canonicalTruncationDomain K α β` with respect to `adelicGLHaar (Fin 2) (𝓞 K) K`;
--
--   $\bullet$ the function $R\mapsto \int_{\mathrm{canonicalTruncationDomain}(K,\alpha,\beta)} \lambda^{\exp R}\varphi_x(x)\,d\,\mathrm{adelicGLHaar}$ tends, as $R\to+\infty$, to $\sum_n c_n\, g\langle \mathrm{tabs}\,n,\mathrm{htabs}\,n\rangle$.
--
--   This is the residual, one-dimensional block of the spectral side of the truncated trace formula for $GL_2$ over $K$ after folding the centre: the kernel built from the characters $\chi\circ\det$ with $\chi^2=\xi_K$, truncated in the second variable and restricted to the diagonal, integrates over the canonical slab domain to an absolutely convergent sum of Hecke-polynomial values at tables that agree outside $S_K$ with Eisenstein eigensystems of pairs of idele class characters. It is used by [`AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul), where this block is combined with the remaining contributions to the folded spectral side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_chiDet_mul_chiDet_inv.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_chiDet_mul_chiDet_inv
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
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} ⊆ X) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      ∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₂ z = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          tabs n v = ((LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).a v,
            (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).b v)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
        (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
        IsUnitFactorization K (SK ∪ T) f faK ff
          (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
            else fSK v) →
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
        IsArchBiFinite K tysK f →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).1 ^ ks v *
            ((HeckeEigensystem.cNorm v)⁻¹ *
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).2) ^ js v) →
        (∀ R : ℝ, IntegrableOn (fun x =>
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x))
            (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
        Filter.Tendsto (fun R : ℝ =>
          ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) Filter.atTop (nhds (∑' n, cs n * g ⟨tabs n, htabs n⟩)) := by sorry
