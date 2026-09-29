-- Prove2me | Theorems.Thm_AutomorphicForm_centralEllipticConstant_eq_of_factorization_of_normFibre_of_exists_ne_zero
-- name    : AutomorphicForm.centralEllipticConstant_eq_of_factorization_of_normFibre_of_exists_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/3754cf14-94d2-50a0-86b4-8eb84eb4387d
-- title:
--   Closed form of the central–elliptic base-change comparison constant
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ a finite Galois extension, $\mathbb{A}_K$, $\mathbb{A}_L$ denote the adele rings, and `AdelicGL2 (𝓞 F) F` is $\mathrm{GL}_2(\mathbb{A}_F)$ with its Borel $\sigma$-algebra and Haar measure `adelicGLHaar`. For an idele $x$, [`NumberField.TateGlobal.ideleNorm F x`](def/NumberField_TateGlobalZeta.html#L19) is the real number given by the distributive Haar character of $x$ acting on $\mathbb{A}_F$, written $\|x\|_F$ below.
--
--   **Slab and fundamental domains on the $L$-side.** Reals $\alpha,\beta$ with $0<\alpha<\beta$ are given, together with a set $\Phi_L\subseteq \mathrm{GL}_2(\mathbb{A}_L)$ contained in the slab $\{g:\|\det g\|_L\in[\alpha,\beta]\}$ (`hΦs`) and which is a fundamental domain (`hΦ`) for the action of the image of $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$ (the map `globalPoints`, induced by $L\to\mathbb{A}_L$) on `adelicGLHaar` restricted to that slab. On the idele units, a Haar measure $\nu_{Z_L}$ on $(\mathbb{A}_L)^\times$ and a set $\Omega_L$ are given with $\Omega_L$ a fundamental domain for the image of $L^\times$ (`hΩL`).
--
--   **Galois data.** $D$ is an [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, compatible with $L\to\mathbb{A}_L$ and continuous in each element; $\sigma\in \mathrm{Gal}(L/K)$ satisfies `hgen`: every $\tau$ lies in the subgroup of integral powers of $\sigma^{-1}$; and `hdeg` asserts that $[L:K]$ is prime.
--
--   **Place bookkeeping.** Finite sets $S_K$ of finite places of $K$ and $S_L$ of finite places of $L$ are given with: `hSL`, every $w$ lying under a place of $S_K$ belongs to $S_L$; `hSsat`, $S_L$ is a union of fibres, i.e. $w\in S_L\leftrightarrow w'\in S_L$ whenever $w,w'$ lie over the same place of $K$; and `hS`, for every $w$ whose place below is outside $S_K$ the ramification index `Ideal.ramificationIdx'` of $w$ over that place is $1$.
--
--   **The character $\xi_L$.** $\xi_L$ is a homomorphism from the full subgroup $\top\le(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the image of $L^\times$ (`hξt`), and satisfies `hξσ`: $\xi_L(\det(\mathtt{heckeGen}\,w))=\xi_L(\det(\mathtt{heckeGen}\,w'))$ for all $w,w'\notin S_L$ lying over the same place of $K$.
--
--   **Level and archimedean types on the $L$-side.** An ideal $N\subseteq\mathcal{O}_L$ is given with `hN`: every $w$ whose prime divides $N$ lies in $S_L$; and an `ArchTypeFamily L` $\mathrm{tys}_L$, i.e. a multiplicity function on the infinite places of $L$ together with, for each such place, that many archimedean representation data.
--
--   Four further functions enter as data: $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, $\varphi_S$ a family on $\mathrm{GL}_2(L\otimes_K K_v)$ indexed by the finite places $v$ of $K$, and $f_{a,K}$, $f_{S,K}$ their $K$-side counterparts; no hypothesis constrains them and they do not occur in the conclusion.
--
--   **The compact set of eigenvalue data.** A set $X$ of functions from finite places of $L$ to $\mathbb{C}\times\mathbb{C}$ is given, compact (`hXc`) and containing (`hX`) all $x$ such that $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$, writing $\eta_w=\xi_L(\det(\mathtt{heckeGen}\,w))$: the second coordinate equals `HeckeEigensystem.cNorm w` $\cdot\,\eta_w$, where `cNorm w` is the absolute norm of $w$ viewed in $\mathbb{C}$; $\|(x_w)_1\|\le(\mathrm{N}w+1)\sqrt{\|\eta_w\|}$; and $\overline{(x_w)_1}=\overline{(x_w)_2}\,\|(x_w)_2\|^{-1}(x_w)_1$.
--
--   **The $K$-side fundamental domains, the character set $\Xi$, level and types.** $\Phi_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ lies in the slab $\{\|\det g\|_K\in[\alpha,\beta]\}$ (`hΦKs`) and is a fundamental domain for the image of $\mathrm{GL}_2(K)$ on `adelicGLHaar` restricted to that slab (`hΦK`); $\nu_{Z_K}$ is a Haar measure on $(\mathbb{A}_K)^\times$ and $\Omega_K$ a fundamental domain for the image of $K^\times$ (`hΩK`). $\Xi$ is a finite set of homomorphisms $\top\le(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ characterised by `hΞ`: $\xi\in\Xi$ if and only if $\xi$ is continuous, trivial on the image of $K^\times$, and $\xi\circ\mathrm{Nm}=\xi_L$, where $\mathrm{Nm}$ is the idelic norm `idelicNorm` of the base change [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87). Finally an ideal $N'\subseteq\mathcal{O}_K$ with `hN'`: every $v$ whose prime divides $N'$ lies in $S_K$, and an `ArchTypeFamily K` $\mathrm{tys}_K$.
--
--   **The constant and the comparison hypothesis.** A complex number $c_0$ is given which satisfies `hgeo`: for every finite $S'\supseteq S_K$ and every pair $(\varphi,f)$ with $\varphi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ continuous, compactly supported and `IsUnitFactorizableAboveOfType K L tysL` for the level $\mathtt{levelOne}(N)\sqcap\mathtt{finiteAdelicGL2Subgroup}\,L$ outside $S'$ (bi-invariance under that subgroup, a semi-local factorisation through archimedean, finite and $v$-adic factors that is the indicator-type product of the $\varphi_{S'}$-factors on elements integral outside $S'$ and vanishes otherwise, and archimedean bi-finiteness of type $\mathrm{tys}_L$), $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ continuous, compactly supported and `IsUnitFactorizableOfTypeAt K tysK` for $\mathtt{principalLevel}(N')\sqcap\mathtt{finiteAdelicGL2Subgroup}\,K$ outside $S'$, the matching condition `AreMatchingAt K L σ.symm S' φ f` (existence of factorisations of $\varphi$ and $f$ whose archimedean factors match in the sense of twisted versus ordinary orbital integrals and whose $v$-factors match for $v\in S'$), and the condition that at each $v\notin S'$ all of whose places above are unramified the indicator of the semi-local integral set matches the indicator of the local integral set (`AreMatchingLocal`), the following identity holds:
--   $$\int_{\Phi_L}\int_{\Omega_L}\xi_L(z)\sum_{\delta}\varphi\big(x^{-1}\,\delta\,{}^{\sigma^{-1}}\!(zx)\big)\,d\nu_{Z_L}\,d\,\mathtt{adelicGLHaar} \;=\; c_0\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\big(K_{\mathrm{cent}}(x,zx)+K_{\mathrm{ell}}(x,zx)\big)\,d\nu_{Z_K}\,d\,\mathtt{adelicGLHaar},$$
--   where on the left $\delta$ runs over the finsum support $\{\delta\in\mathrm{GL}_2(L)$ : the $\sigma^{-1}$-twisted norm class of $\delta$ under [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) is the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ that is either elliptic (its characteristic polynomial has no root in $K$) or central (a scalar matrix)$\}$, $\delta$ is inserted via `globalPoints`, ${}^{\sigma^{-1}}\!(\cdot)$ is `sigmaAdelicAct K L D σ.symm`, and $z$ acts by the scalar embedding `centralScalar`; and on the right $K_{\mathrm{cent}}$, $K_{\mathrm{ell}}$ are `adelicKernelCentralPart K f` and `adelicKernelEllipticPart K f`, the finsums of $f(x^{-1}\gamma y)$ over central, respectively elliptic, $\gamma\in\mathrm{GL}_2(K)$.
--
--   **Non-degeneracy.** `hex` asserts the existence of one finite $S'\supseteq S_K$ and one pair $(\varphi,f)$ satisfying all the admissibility conditions listed in `hgeo` and for which the $K$-side sum $\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)(K_{\mathrm{cent}}+K_{\mathrm{ell}})$ is non-zero.
--
--   **Haar factorisation constants.** Positive reals $c_K,c_L$ are given with: `hG`, for every finite set $S$ of finite places of $K$ and every $f$, $f_a$, $(f_S)$ with the stated measurability, if $f(g)=f_a(g_\infty)\prod_{v\in S}f_S^v(g_v)$ whenever all components of $g$ outside $S$ lie in `localIntegralSet` and $f(g)=0$ whenever some component outside $S$ does not, then $\int f\,d\,\mathtt{adelicGLHaar}=c_K\big(\int f_a\,d\,\mathtt{archHaarK}\big)\prod_{v\in S}\int f_S^v\,d\,\mathtt{localHaar}$; and `hG'`, the analogous factorisation with constant $c_L$ for the pushforward of `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_L)$ to $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ along the map induced by the inverse of the composite of `Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)` with [`M4aHerbrand.Bridge.genuineRingEquiv K L`](def/M4aHerbrand_GenuineTensorEquiv.html#L57), with `archHaarL` and the semi-local measures `semiLocalHaar` in place of `archHaarK` and `localHaar` and `semiLocalIntegralSet` in place of `localIntegralSet`.
--
--   **The base-change subgroup and the norm-one subgroup.** $A_K\le(\mathbb{A}_L)^\times$ is closed (`hAKc`) and consists exactly of the images of $(\mathbb{A}_K)^\times$ under the unit map of the $\beta$-component of `genuineBaseChange K L` (`hAK`); $\mu_{A_K}$ is a Haar measure on $A_K$ with `hμAK`: integration over $A_K$ of any $g$ agrees with integration over $(\mathbb{A}_K)^\times$ against $\nu_{Z_K}$ of $g$ composed with that map. $N^1\le(\mathbb{A}_L)^\times$ is closed (`hN1c`) and is exactly the kernel of the idelic norm (`hN1`); $\mu_N$ is a Haar measure on $N^1$, and a positive constant $c_N$ satisfies `hNc`: for every $g$, $\int_{N^1}g=c_N\int_{(\mathbb{A}_L)^\times/A_K}g\big(({}^{\sigma^{-1}}q)\,q^{-1}\big)$, the quotient being the orbit space of the $A_K$-action with the measure [`HaarQuotient.measure νZL AK μAK`](def/HaarQuotient.html#L28), $q$ a chosen representative and ${}^{\sigma^{-1}}(\cdot)$ the action `D.unitsAct σ.symm`.
--
--   **The norm-fibre constant.** A positive real $C$ satisfies: `hCl`, for every measurable $g:(\mathbb{A}_K)^\times\to[0,\infty]$, the lower integral over the orbit space $(\mathbb{A}_L)^\times/N^1$ with measure [`HaarQuotient.measure νZL N1 μN`](def/HaarQuotient.html#L28) of $g$ evaluated at the idelic norm of a representative equals $\mathtt{ENNReal.ofReal}\,C$ times the lower integral of $g$ over the range of the idelic norm against $\nu_{Z_K}$; and `hCi`, for every measurable complex-valued $g$, integrability on that quotient of the same composite is equivalent to integrability of $g$ on the range of the idelic norm against $\nu_{Z_K}$, and the two integrals differ by the factor $C$.
--
--   **Conclusion.** Under these hypotheses the constant $c_0$ is determined:
--   $$c_0=\Big(\frac{c_L}{c_K}\,c_N\,C\,\frac{\nu_{Z_L}\big(\Omega_L\cap\{z:\|z\|_L\in[1,e]\}\big)}{\nu_{Z_K}\big(\Omega_K\cap\{a:\|a\|_K\in[1,e]\}\big)}\cdot\frac{1}{\max(1,|\Xi|)}\Big),$$
--   the two measures being taken as real numbers via `ENNReal.toReal`, the maximum taken among natural numbers and then cast, and the whole real number coerced into $\mathbb{C}$.
--
--   This is the normalisation step in the comparison of the central and elliptic contributions of the twisted trace formula for $\mathrm{GL}_2$ over $L$ with the ordinary one over $K$, for $L/K$ cyclic of prime degree: the proportionality constant postulated in `hgeo` is pinned down, once a single matched test pair with non-vanishing $K$-side contribution exists, as an explicit product of the two adelic Haar factorisation constants, the Hilbert-90 normalisation $c_N$, the norm-fibre constant $C$, the ratio of the idele-class volumes of the unit slab, and the reciprocal of $\max(1,|\Xi|)$. It feeds the comparison of the weighted hyperbolic terms along Hecke words, where the same constant must appear on both sides for the cancellation to take place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_centralEllipticConstant_eq_of_factorization_of_normFibre_of_exists_ne_zero.lean

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.centralEllipticConstant_eq_of_factorization_of_normFibre_of_exists_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (hdeg : (Module.finrank K L).Prime)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (c₀ : ℂ)
    (hgeo :
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
        (_hφt : AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (_hft : AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f)
        (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
        (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
        (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        c₀ * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))

    (hex : ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧
      ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ),
        Continuous φ ∧ HasCompactSupport φ ∧
        AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧
        Continuous f ∧ HasCompactSupport f ∧
        AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧
        AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧
        (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0)

    (cK cL : ℝ) (hcK : 0 < cK) (hcL : 0 < cL)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa (AutomorphicForm.archHaarK K) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v) (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉ AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = cK * (∫ x, fa x ∂(AutomorphicForm.archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa (AutomorphicForm.archHaarL K L) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v) (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) * ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) → F x = 0) →
          ∫ x, F x ∂(@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) (Matrix.GeneralLinearGroup.map (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom)) (adelicGLHaar (Fin 2) (𝓞 L) L)) = cL * (∫ y, Fa y ∂(AutomorphicForm.archHaarL K L)) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))

    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νZK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ.symm q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))

    (C : ℝ) (hC : 0 < C)
    (hCl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ENNReal, Measurable g →
        ∫⁻ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          ENNReal.ofReal C *
            ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hCi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
        (Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
            (HaarQuotient.measure νZL N1 μN) ↔
          IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          C * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK) :
    c₀ = (((cL / cK) * cN * C * (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal / (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal / ((max 1 Ξ.card : ℕ) : ℝ) : ℝ) : ℂ) := by sorry
