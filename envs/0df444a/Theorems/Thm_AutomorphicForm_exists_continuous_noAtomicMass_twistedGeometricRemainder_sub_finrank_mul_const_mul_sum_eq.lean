-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_noAtomicMass_twistedGeometricRemainder_sub_finrank_mul_const_mul_sum_eq
-- name    : AutomorphicForm.exists_continuous_noAtomicMass_twistedGeometricRemainder_sub_finrank_mul_const_mul_sum_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/c5cc0485-de5a-56a0-b1cf-3d4b7883c256
-- title:
--   Twisted geometric remainder minus [L:K]λ times slot sum: cylinder-small functional
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ finite Galois, and $\mathrm{GL}_2$ of the adeles of $F$ is written `AdelicGL2 (𝓞 F) F`; `globalPoints` denotes the map $\mathrm{GL}_2(F)\to \mathrm{GL}_2(\mathbb{A}_F)$, `centralScalar` the map sending an idele to the corresponding scalar matrix, `heckeGen` the adelic Hecke generator at a finite place, and `ideleNorm` the idelic modulus computed from the distributive Haar character.
--
--   **Geometric data.** Real numbers $\alpha<\beta$ with $0<\alpha$ are fixed. On the $L$-side, $\Phi_L\subseteq \mathrm{GL}_2(\mathbb{A}_L)$ is contained in the determinant slab $\{g\mid \mathrm{ideleNorm}_L(\det g)\in[\alpha,\beta]\}$ (`hΦs`) and is a fundamental domain for the image of $\mathrm{GL}_2(L)$ with respect to `adelicGLHaar` restricted to that slab (`hΦ`); $\nu_{Z,L}$ is a Haar measure on $(\mathbb{A}_L)^\times$ (for a Borel measurable structure on the ideles) and $\Omega_L$ a fundamental domain for the image of $L^\times$ in $(\mathbb{A}_L)^\times$ (`hΩL`). The same data $\Phi_K\subseteq$ slab (`hΦKs`, `hΦK`), $\nu_{Z,K}$, $\Omega_K$ (`hΩK`) are fixed on the $K$-side.
--
--   **Galois data.** $D$ is a datum [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, continuous and compatible with the structure map of $L$; $\sigma\in \mathrm{Gal}(L/K)$ is such that $\sigma^{-1}$ generates the group (`hgen`: every $\tau$ lies in the integral powers of $\sigma^{-1}$), and $[L:K]$ is prime (`hdeg`). The action of $\sigma^{-1}$ on $\mathrm{GL}_2(\mathbb{A}_L)$ obtained from $D$ entrywise is `sigmaAdelicAct K L D σ.symm`.
--
--   **Place data.** $S_K$ is a finite set of finite places of $K$ and $S_L$ one of finite places of $L$, with: every $w$ lying over a place of $S_K$ belongs to $S_L$ (`hSL`); membership in $S_L$ depends only on the place of $K$ below (`hSsat`); and for every $w$ whose place below is outside $S_K$ the ramification index is $1$ (`hS`).
--
--   **Central character.** $\xi_L$ is a character of the full subgroup of $(\mathbb{A}_L)^\times$ with values in $\mathbb{C}^\times$, continuous (`hξc`), trivial on the image of $L^\times$ (`hξt`), and taking equal values on $\det(\mathrm{heckeGen}\,w)$ and $\det(\mathrm{heckeGen}\,w')$ whenever $w,w'\notin S_L$ lie over the same place of $K$ (`hξσ`). An ideal $N$ of $\mathcal{O}_L$ is fixed with every $w$ dividing $N$ in $S_L$ (`hN`), and an ideal $N'$ of $\mathcal{O}_K$ with every $v$ dividing $N'$ in $S_K$ (`hN'`). Archimedean type families $\mathrm{tys}_L$, $\mathrm{tys}_K$ are fixed (for each infinite place, a finite list of representations of the relevant local group). $\Xi$ is a finite set of characters of the full subgroup of $(\mathbb{A}_K)^\times$, and `hΞ` states that a character belongs to $\Xi$ exactly when it is continuous, trivial on the image of $K^\times$, and pulls back along the idelic norm of the base-change datum [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87) to $\xi_L$.
--
--   **Test functions and factorisations.** $\varphi_a$, $\varphi_S$ are an archimedean factor on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$ and semi-local factors on $\mathrm{GL}_2(L\otimes_K K_v)$; $f_{a,K}$, $f_{S,K}$ are the corresponding data for $K$. A continuous, compactly supported $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ satisfies `IsUnitFactorizableAboveOfType` above $S_K$ for the level `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` and type $\mathrm{tys}_L$ (`hφt`), that is, the predicate `IsUnitFactorizableAbove` together with $\varphi$ and $g\mapsto\varphi(g^{-1})$ lying in the archimedean cut submodules of $\mathrm{tys}_L$; a continuous, compactly supported $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ satisfies the corresponding `IsUnitFactorizableOfTypeAt` for `principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K` and $\mathrm{tys}_K$ (`hft`). Furthermore $\varphi$ and $f$ match at $\sigma^{-1}$ over $S_K$ (`hm`: existence of archimedean, finite and semi-local factorisations of $\varphi$, a unit factorisation of $f$, archimedean matching, and local matching at each $v\in S_K$), and $\varphi$, $f$ admit factorisations with the prescribed factors: `hφfac` asserts a finite factor $\varphi_f$ with `IsSemiLocalFactorization K L SK φ φa φf φS` (an archimedean test factor, a locally constant compactly supported finite factor, semi-local test functions at the places of $S_K$, the product formula for $\varphi_f$ on elements integral outside $S_K$, vanishing otherwise, and $\varphi(g)=\varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$), and `hffac` the analogous `IsUnitFactorization` for $f$ with $f_{a,K}$, $f_{S,K}$.
--
--   **Comparison hypothesis.** A constant $c_0\in\mathbb{C}$ is fixed, together with the central–elliptic comparison `hgeo`: for every finite $S'\supseteq S_K$ and every pair of continuous compactly supported test functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ which are unit-factorizable of the stated types and levels above $S'$, match at $\sigma^{-1}$ over $S'$, and are such that at every $v\notin S'$ all of whose places above are unramified the indicator functions of `semiLocalIntegralSet K L v` and `localIntegralSet K v` match locally, the $\xi_L$-weighted double integral over $\Phi_L\times\Omega_L$ of $\sum_\delta \varphi(x^{-1}\,\delta\,\sigma^{-1}(zx))$, the sum running over those $\delta\in \mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted norm class `normClassMap hgen` is the conjugacy class of some $\gamma\in \mathrm{GL}_2(K)$ that is elliptic (characteristic polynomial without root in $K$) or central (a scalar matrix), equals $c_0$ times $\sum_{\xi_K\in\Xi}$ of the corresponding $\xi_K$-weighted integral over $\Phi_K\times\Omega_K$ of the sum of the central and elliptic parts of the adelic kernel of $f$ at $(x,\ \mathrm{centralScalar}(z)x)$.
--
--   **Satake box.** $X$ is a compact set of functions from the finite places of $L$ to $\mathbb{C}\times\mathbb{C}$ (`hXc`) which contains (`hX`) every $x$ such that $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$, writing $\xi_L(w)=\xi_L(\det \mathrm{heckeGen}\,w)$: the second coordinate is $\mathrm{cNorm}(w)\,\xi_L(w)$ with $\mathrm{cNorm}(w)=|\mathcal{O}_L/w|$, the first coordinate satisfies $\|(x_w)_1\|\le (|\mathcal{O}_L/w|+1)\sqrt{\|\xi_L(w)\|}$, and $\overline{(x_w)_1}=\bigl(\overline{(x_w)_2}/\|(x_w)_2\|\bigr)(x_w)_1$.
--
--   **Conclusion.** There exists $\lambda\in\mathbb{C}$ with the following three properties.
--
--   (i) $\lambda\neq 0$.
--
--   (ii) If there exist a finite $S'\supseteq S_K$ and test functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, both continuous and compactly supported, unit-factorizable of type $\mathrm{tys}_L$ above $S'$ for `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` respectively of type $\mathrm{tys}_K$ at $S'$ for `principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K`, matching at $\sigma^{-1}$ over $S'$, with unit matching at every $v\notin S'$ whose places above are unramified, and such that $\sum_{\xi_K\in\Xi}$ of the $\xi_K$-weighted integral over $\Phi_K\times\Omega_K$ of the central plus elliptic part of the adelic kernel of that $f$ is non-zero, then $[L:K]\cdot\lambda=c_0$ in $\mathbb{C}$.
--
--   (iii) For every finite set $T$ of finite places of $K$ disjoint from $S_K$ with $\#T\ge 2$ such that no place of $L$ above a place of $T$ lies in $S_L$; for every choice $ws$ of an extension $(ws\,v)\in v.\mathrm{Extension}(\mathcal{O}_L)$ for each $v$ and every map $w'$ from places of $K$ to places of $L$ with $(w'v)$ the $\sigma^{-1}$-translate of $(ws\,v)$ for $v\in T$; for every family $\varpi_s$ of elements of the valuation rings of the completions $L_{ws\,v}$ that are irreducible for $v\in T$ and non-zero in $L_{ws\,v}$, every $n_s$, every family $rT_s$ of finite systems $\mathrm{Fin}(n_s v)\to \mathrm{GL}_2(L_{ws\,v})$ forming a Hecke coset system ([`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15)) for the integral subgroup and the element $\mathrm{diag}(\varpi_s v,1)$, and every family $z_s$ of central elements equal to $\varpi_s v$ times the identity matrix for $v\in T$; and for the analogous data $\varpi_{K,s}$, $n_{K,s}$, $r_{K,s}$, $z_{K,s}$ on the $K$-side over the completions $K_v$ — there exists a continuous $\mathbb{C}$-linear functional $\Delta : C(X,\mathbb{C})\to\mathbb{C}$ such that:
--
--   (iii.a) ($\Delta$ carries no atomic mass on the $T$-cylinders.) For every $\tau$ assigning to each place of $K$ a point of $\mathbb{C}\times\mathbb{C}$ and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb{C}\times\mathbb{C}$, open and containing $\tau_v$ for $v\in T$, such that $\|\Delta g\|<\varepsilon$ for every $g\in C(X,\mathbb{C})$ with $\|g\|\le 1$ pointwise which vanishes at every $y\in X$ for which $y(w'v)\notin U_v$ for some $v\in T$.
--
--   (iii.b) For all exponent families $ks,js$ of natural numbers; for every continuous compactly supported $\varphi_L$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and every finite factor $\varphi_f$ such that `IsSemiLocalFactorization K L (SK ∪ T) φL φa φf` holds with semi-local factors equal to $\varphi_S v$ for $v\notin T$ and, for $v\in T$, to the Hecke-word function $x\mapsto \sum_{\iota:\mathrm{Fin}(ks\,v)\to\mathrm{Fin}(n_s v)}\mathbf 1_{\mathrm{semiLocalIntegralSet}}\bigl(\mathrm{semiLocalComponent}(\mathrm{localEmbed}(\prod_m rT_s v(\iota m)\cdot (z_s v)^{js\,v}))^{-1}x\bigr)$, and such that $\varphi_L$ is bi-invariant under `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` and archimedean bi-finite of type $\mathrm{tys}_L$; and for every family $\mathrm{fam}$ of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ indexed by the slot indices $m\in \mathrm{SatakeCombination.slotIndex}\ K\ L\ ws\ ks\ js\ T$ (the functions assigning to each $v\in T$ an exponent pair in the support of the corresponding slot word) such that for each such $m$: $\mathrm{fam}\,m$ is bi-invariant under `principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K`, archimedean bi-finite of type $\mathrm{tys}_K$, $f_{a,K}$ is an archimedean test factor, each $f_{S,K}v$ for $v\in S_K$ is a local test function, and there is a finite test factor $f_f$ (locally constant with compact support) which on elements integral outside $S_K\cup T$ equals the product over $v\in S_K\cup T$ of the local factors — at $v\in T$ the Hecke-word function built from $r_{K,s}v$ with $m(v)_0$ factors and $(z_{K,s}v)^{m(v)_1}$, and $f_{S,K}v$ otherwise — evaluated at the component at $v$, vanishes on elements with some component outside $S_K\cup T$ non-integral, and satisfies $\mathrm{fam}\,m\,(g)=f_{a,K}(g_\infty)f_f(g_{\mathrm{fin}})$: then for every $g\in C(X,\mathbb{C})$ given by $g(x)=\prod_{v\in T} (x(w'v))_1^{\,ks\,v}\bigl(\mathrm{cNorm}(w'v)^{-1}(x(w'v))_2\bigr)^{js\,v}$,
--   $$\mathrm{twistedGeometricRemainder}\bigl(D,\sigma^{-1},\Phi_L,\Phi_{0,L},\nu_{Z,L},\Omega_L,\xi_L,\varphi_L\bigr)\;-\;[L:K]\,\lambda\sum_{\xi_K\in\Xi}\ \sum_{m}\ \mathrm{slotFamilyCoeff}(m)\,\mathrm{geometricRemainder}\bigl(\Phi_K,\Phi_{0,K},\nu_{Z,K},\Omega_K,\xi_K,\mathrm{fam}\,m\bigr)\;=\;\Delta g,$$
--   where $\Phi_{0,L}$ and $\Phi_{0,K}$ are the canonical truncation domains [`AutomorphicForm.canonicalTruncationDomain`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) of the slab $[\alpha,\beta]$ for $L$ and for $K$, the inner sum runs over the slot indices $m$ as above, $\mathrm{slotFamilyCoeff}$ is the product over $v\in T$ of the slot coefficients `SatakeCombination.slotCoeff`, and both remainders are the half-line intercepts $\lim_{R\to\infty}\bigl(F(R)-R\cdot\mathrm{slope}\,F\bigr)$ of the function of $R$ given by the $\xi$-weighted integral over the canonical truncation domain of the truncation [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) at height $e^R$ of the kernel — the twisted kernel `twistedAdelicKernel` formed with the $\sigma^{-1}$-action in the $L$-case, the kernel `adelicKernel` in the $K$-case — minus the corresponding central-plus-elliptic term over $\Phi_L$, respectively $\Phi_K$.
--
--   This is the $\Delta$-functional step in the comparison of the twisted (base-change) geometric side over $L$ with the Satake-expanded geometric side over $K$ for a cyclic extension of prime degree: after Hecke words at an auxiliary set $T$ of places are inserted, the difference of the two geometric remainders is realised as the value at an explicit monomial of a continuous linear functional on continuous functions on the compact Satake box $X$, with the cylinder-smallness property expressing that this functional carries no atomic mass at any prescribed point. It is used by the statement producing atoms for the Hecke-word twisted cut traces, the input to the eigensystem-matching step of cyclic base change for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_noAtomicMass_twistedGeometricRemainder_sub_finrank_mul_const_mul_sum_eq.lean

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

theorem
    AutomorphicForm.exists_continuous_noAtomicMass_twistedGeometricRemainder_sub_finrank_mul_const_mul_sum_eq
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
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (hft : IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f)
    (hm : AreMatchingAt K L σ.symm SK φ f)
    (hφfac : ∃ φf, IsSemiLocalFactorization K L SK φ φa φf φS)
    (hffac : ∃ ff, IsUnitFactorization K SK f faK ff fSK)
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
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ((∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧ ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous φ ∧ HasCompactSupport φ ∧ AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧ Continuous f ∧ HasCompactSupport f ∧ AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧ AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧ (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' → (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) → AutomorphicForm.AreMatchingLocal K L v σ.symm ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧ (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) + AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) → (Module.finrank K L : ℂ) * lam = c₀) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
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
      ∃ Δ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Δ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ) (hφL : Continuous φL) (hφLc : HasCompactSupport φL)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φL →
        IsArchBiFinite L tysL φL →
      ∀ fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ,
        (∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fam m) ∧
          IsArchBiFinite K tysK (fam m) ∧
          IsArchTestFactor K faK ∧
          (∀ v ∈ SK, IsLocalTestFn K v (fSK v)) ∧
          ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
            IsFinTestFactor K ff ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
                ff h = ∏ v ∈ SK ∪ T,
                  (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                    else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) →
                ff h = 0) ∧
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)
        ) →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
      twistedGeometricRemainder K L D σ.symm hgen ΦL (AutomorphicForm.canonicalTruncationDomain L α β) νZL ΩL ξL φL -
        (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            geometricRemainder K ΦK
              (AutomorphicForm.canonicalTruncationDomain K α β) νZK ΩK ξK (fam m) =
        Δ g := by sorry
