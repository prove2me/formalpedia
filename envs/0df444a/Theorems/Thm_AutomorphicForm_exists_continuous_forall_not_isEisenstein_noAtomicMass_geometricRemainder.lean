-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_forall_not_isEisenstein_noAtomicMass_geometricRemainder
-- name    : AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_geometricRemainder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/ef8d3bf3-199d-5c2d-b465-7addd2d03cb1
-- title:
--   Atom-free trace identity with geometric remainder for GL₂
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, let $\Phi_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ be arbitrary, and let $c_K>0$, $u_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ be such that the union of the right translates $(\cdot\,x)$ of the centre-cut Siegel set (finite part integral, each local height $\ge c_K$, each window $\mathrm{xWindowSq}\le u_K^2$, each archimedean determinant norm in $[d_{1K},d_{2K}]$) covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left multiplication by global points and right multiplication by central idelic scalars. Fix a Haar measure $\nu_{ZK}$ on the ideles, a fundamental domain $\Omega_K$ for the image of $K^\times$, a finite set $S_K$ of finite places, a character $\xi_K$ of the idele group (as a homomorphism on the top subgroup) whose associated function is continuous and trivial on principal ideles, an ideal $N$ all of whose prime divisors lie in $S_K$, an archimedean type family $\mathrm{tys}_K$, an archimedean factor $f_{aK}$, local factors $f_{SK}$, and a compact set $X$ of tables $x\colon v\mapsto (x_v^{(1)},x_v^{(2)})\in\mathbb{C}^2$ containing every table that vanishes on $S_K$ and satisfies, for $v\notin S_K$, $x_v^{(2)}=\mathrm{N}(v)\,\xi_K(\det\mathrm{heckeGen}_v)$, $\|x_v^{(1)}\|\le(\mathrm{N}(v)+1)\sqrt{\|\xi_K(\det\mathrm{heckeGen}_v)\|}$ and $\overline{x_v^{(1)}}=(\overline{x_v^{(2)}}/\|x_v^{(2)}\|)\,x_v^{(1)}$. Then two things hold. First, the band constant $\nu_{ZK}(\Omega_K\cap\{z:\ \mathrm{ideleNorm}(\det(z\cdot 1))\in[\alpha,\beta]\})$, read as a real and then as a complex number, is nonzero. Second, there are tables $t_n\in X$ and masses $c_n\in\mathbb{C}$ $(n\in\mathbb{N})$ with $\sum_n\|c_n\|<\infty$ such that whenever $c_n\ne 0$ there exist a nonzero ideal $M$ and homomorphisms $\chi_1,\chi_2$ from the ideles to $\mathbb{C}^\times$, both continuous, trivial on principal ideles and unramified at every $v\notin S_K$, with $t_n$ agreeing outside $S_K$ with the pair $(a_v,b_v)$ of the Eisenstein eigensystem $\mathrm{eisensteinTableOf}\,M\,\chi_1\,\chi_2$ (so $a_v=\chi_1(\varpi_v)+\chi_2(\varpi_v)$, $b_v=\chi_1(\varpi_v)\chi_2(\varpi_v)$ for uniformizer ideles); and, moreover, for every finite set $T$ of finite places disjoint from $S_K$ with $|T|\ge 2$, every family of uniformisers $\varpi_v$ (irreducible and nonzero in the completion for $v\in T$), every family of coset representatives $r_{Ks}$ forming a Hecke coset system for the double coset of $\mathrm{diagPi}(\varpi_v)$ relative to the integral subgroup of $\mathrm{GL}_2(K_v)$, and every family $z_{Ks}$ with $z_{Ks,v}=\varpi_v\cdot 1$ for $v\in T$, there is a continuous linear functional $\Lambda$ on $C(X,\mathbb{C})$ with no atomic mass — for every table $\tau$ and every $\varepsilon>0$ there are sets $U_v$, open and containing $\tau_v$ for $v\in T$, such that $\|\Lambda g\|<\varepsilon$ for every $g$ bounded by $1$ in absolute value that vanishes at all $y\in X$ whose coordinate at some $v\in T$ lies outside $U_v$ — such that for all exponent families $k_s,j_s$, every continuous compactly supported $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ admitting a unit factorisation over $S_K\cup T$ with archimedean factor $f_{aK}$, finite factor $ff$, local factors $f_{SK,v}$ off $T$ and, at $v\in T$, the Hecke-word factor $x\mapsto\sum_{\iota}\mathbf{1}_{\mathrm{localIntegralSet}}\big((\prod_m r_{Ks,v}(\iota m)\cdot z_{Ks,v}^{j_{s,v}})^{-1}x\big)$, bi-invariant under the principal level $N$ intersected with the finite adelic subgroup and archimedean bi-finite of type $\mathrm{tys}_K$, and every $g\in C(X,\mathbb{C})$ given by $g(x)=\prod_{v\in T}(x_v^{(1)})^{k_{s,v}}\big(\mathrm{N}(v)^{-1}x_v^{(2)}\big)^{j_{s,v}}$, the quantity $$\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\big(\mathrm{adelicKernelCentralPart}(f)(x,z x)+\mathrm{adelicKernelEllipticPart}(f)(x,z x)\big)\,d\nu_{ZK}\,d\mu_{\mathrm{Haar}}$$ minus the band constant times $\sum_{\pi}\mathrm{cutTrace}(\pi)(f)$, the sum running over the cuspidal classes for the production pins attached to the Siegel covering, the principal levels intersected with the finite adelic subgroup, the Hecke generators and the adelic box, equals $\sum_n c_n\,g(t_n)+\Lambda g-\mathrm{geometricRemainder}(K,\Phi_K,\mathrm{canonicalTruncationDomain}(\alpha,\beta),\nu_{ZK},\Omega_K,\xi_K,f)$.
--
--   This is the comparison, on Hecke words at places outside the ramification set, between the central and elliptic geometric contributions to the twisted adelic kernel and the cuspidal cut traces: the discrepancy is split into an absolutely summable atomic part carried by Eisenstein eigensystem tables, a functional with no atomic mass at the places of $T$, and the geometric remainder of the truncation. It is used in the deduction of identities for twisted cut traces against Hecke word sums and in the fibre-sum comparison at central elliptic elements for prime parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_forall_not_isEisenstein_noAtomicMass_geometricRemainder.lean

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

theorem
    AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_geometricRemainder
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
    ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) ≠ 0 ∧
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
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
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
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).2) ^ js v) → (
  ∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
        AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
    ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
          ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
          ∑' π : {π : HeckeEigensystem K ℂ //
              π ∈ cuspClasses K
                (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK},
            cutTrace K
              (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π.1 tysK f hf hfc =
          ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g -
            AutomorphicForm.geometricRemainder K ΦK (AutomorphicForm.canonicalTruncationDomain K α β)
              νZK ΩK ξK f) := by sorry
