-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform
-- name    : AutomorphicForm.exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/cdd23b53-bedc-570f-98a4-9c6e382afc9c
-- title:
--   Comparison of parabolic intercepts along Hecke words, uniform λ
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields and let $0<\alpha<\beta$ be real numbers.
--
--   **Global data on the side of $L$.** $\Phi_L$ is a subset of $\mathrm{GL}_2(\mathbb{A}_L)$ (written `AdelicGL2 (𝓞 L) L`) contained in the determinant slab $\{g \mid \mathrm{ideleNorm}_L(\det g)\in[\alpha,\beta]\}$, where [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) is the distributive Haar character of the idele in question, and $\Phi_L$ is a fundamental domain for the range of `globalPoints (𝓞 L) L` (the image of $\mathrm{GL}_2(L)$ under the structure map $L\to\mathbb{A}_L$) with respect to the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` restricted to that slab. Further, $\nu_{Z,L}$ is a Haar measure on $(\mathbb{A}_L)^\times$ and $\Omega_L$ a fundamental domain for the range of the principal ideles $L^\times\to(\mathbb{A}_L)^\times$ with respect to $\nu_{Z,L}$. $D$ is an idele Galois descent datum for $L/K$: a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, compatible with $L\to\mathbb{A}_L$ and continuous in each argument. $\sigma$ is a $K$-automorphism of $L$ such that every $\tau\in\mathrm{Gal}(L/K)$ lies in the group of integer powers of $\sigma^{-1}$ (hypothesis `hgen`), and $[L:K]$ is prime (`hdeg`).
--
--   **Place sets.** $S_K$ is a finite set of finite places of $K$ and $S_L$ a finite set of finite places of $L$, subject to: every place of $L$ lying over a place in $S_K$ belongs to $S_L$ (`hSL`); membership of $S_L$ depends only on the place of $K$ below (`hSsat`); and every place of $L$ whose place below is outside $S_K$ has ramification index $1$ (`hS`).
--
--   **The character $\xi_L$.** $\xi_L$ is a homomorphism from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the principal ideles (`hξt`), and takes the same value on $\det(\mathrm{heckeGen}_w)$ and $\det(\mathrm{heckeGen}_{w'})$ whenever $w,w'\notin S_L$ lie over the same place of $K$ (`hξσ`).
--
--   **Levels, types and local factors.** $N$ is an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`); $N'$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN'`); $\mathrm{tys}_L$, $\mathrm{tys}_K$ are archimedean type families (for each infinite place, a finite list of archimedean representation types); $\varphi_a$ is a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, $\varphi_{S}$ a family of functions on $\mathrm{GL}_2(L\otimes_K K_v)$ indexed by the finite places $v$ of $K$, and $f_{a,K}$, $f_{S,K}$ the corresponding data on the side of $K$.
--
--   **The compact set of tables.** $X$ is a compact set of functions from the finite places of $L$ to $\mathbb{C}\times\mathbb{C}$, and hypothesis `hX` requires $X$ to contain every table $x$ such that $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$: the second coordinate equals $\mathrm{cNorm}(w)\,\xi_L(\det \mathrm{heckeGen}_w)$ with $\mathrm{cNorm}(w)=|\mathcal{O}_L/w|$; the first coordinate satisfies $\|(x_w)_1\|\le(|\mathcal{O}_L/w|+1)\sqrt{\|\xi_L(\det\mathrm{heckeGen}_w)\|}$; and $\overline{(x_w)_1}=\bigl(\overline{(x_w)_2}/\|(x_w)_2\|\bigr)(x_w)_1$.
--
--   **Global data on the side of $K$.** $\Phi_K$ is contained in the corresponding determinant slab of $\mathrm{GL}_2(\mathbb{A}_K)$ and is a fundamental domain for the image of $\mathrm{GL}_2(K)$ with respect to the adelic Haar measure restricted to that slab; $\nu_{Z,K}$ is a Haar measure on $(\mathbb{A}_K)^\times$ and $\Omega_K$ a fundamental domain for the principal ideles of $K$. $\Xi$ is a finite set of homomorphisms from the full subgroup of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ characterised by `hΞ`: $\xi\in\Xi$ if and only if $\xi$ is continuous, trivial on the principal ideles of $K$, and satisfies $\xi(\mathrm{idelicNorm}(z))=\xi_L(z)$ for all $z\in(\mathbb{A}_L)^\times$, the norm being the idelic norm of the base change [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87).
--
--   **The geometric comparison constant.** $c_0$ is a complex number, and hypothesis `hgeo` states the comparison of the central and elliptic terms: for every finite set $S'\supseteq S_K$ of places of $K$, every continuous compactly supported $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ satisfying `IsUnitFactorizableAboveOfType` for $\mathrm{tys}_L$, the level `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` and $S'$ (that is, `IsUnitFactorizableAbove` together with arch-bi-finiteness for $\mathrm{tys}_L$), every continuous compactly supported $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ satisfying `IsUnitFactorizableOfTypeAt` for $\mathrm{tys}_K$, the level `principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K` and $S'$, which match at $\sigma^{-1}$ over $S'$ in the sense of `AreMatchingAt`, and such that at every $v\notin S'$ all of whose places above are unramified the indicator functions of `semiLocalIntegralSet K L v` and `localIntegralSet K v` match locally, one has
--   $$\int_{\Phi_L}\int_{\Omega_L}\xi_L(z)\sum_{\delta}\varphi\bigl(x^{-1}\,\delta\,\sigma^{-1}_{\mathbb{A}}(z\cdot x)\bigr)\,d\nu_{Z,L}\,d\mu_L = c_0\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\bigl(K^{\mathrm{cent}}_f(x,z x)+K^{\mathrm{ell}}_f(x,z x)\bigr)\,d\nu_{Z,K}\,d\mu_K,$$
--   where $\delta$ runs over those elements of $\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted norm class `normClassMap hgen` is the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ lying in the elliptic cell or the central cell, $\sigma^{-1}_{\mathbb{A}}$ denotes `sigmaAdelicAct K L D σ.symm`, $z$ is inserted as the central scalar matrix, and $K^{\mathrm{cent}}_f$, $K^{\mathrm{ell}}_f$ are the finsums of $f(x^{-1}\gamma y)$ over $\gamma$ in the central, respectively elliptic, cell.
--
--   **Conclusion.** There exists $\lambda\in\mathbb{C}$, $\lambda\ne0$, with the following two properties.
--
--   *(i)* If there exist a finite $S'\supseteq S_K$ and functions $\varphi$, $f$ satisfying exactly the list of conditions appearing in `hgeo` (continuity, compact support, unit factorizability above $S'$ of type $\mathrm{tys}_L$ at level `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`; continuity, compact support, unit factorizability at $S'$ of type $\mathrm{tys}_K$ at level `principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K`; matching at $\sigma^{-1}$ over $S'$; and the local matching of the two integral-set indicators at unramified places outside $S'$) for which the $K$-side sum $\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\bigl(K^{\mathrm{cent}}_f+K^{\mathrm{ell}}_f\bigr)$ is nonzero, then $[L:K]\cdot\lambda=c_0$.
--
--   *(ii)* For every finite set $T$ of finite places of $K$ disjoint from $S_K$ with $|T|\ge2$ such that no place of $L$ above a place of $T$ lies in $S_L$; every choice $\mathrm{ws}$ assigning to each place $v$ of $K$ a place of $L$ above $v$; every map $w'$ from places of $K$ to places of $L$ with $(w'v)$ the ideal $\sigma^{-1}\cdot(\mathrm{ws}\,v)$ for $v\in T$; every family $\varpi$ of elements of the valuation rings at the $\mathrm{ws}\,v$ which are irreducible for $v\in T$ and have nonzero image in the completion; every $n$ and every family $r_T$ with $r_T v:\mathrm{Fin}(n_v)\to\mathrm{GL}_2(L_{\mathrm{ws}\,v})$ a Hecke coset system (representatives lying in, covering modulo the subgroup, and injective modulo the subgroup of, the double coset of [`LocalGL2.diagPi (ϖs v)`](def/LocalLanglands_HeckeCosetLocal.html#L68) relative to the image of $\mathrm{GL}_2$ of the valuation ring) for $v\in T$; every family $z_s$ with $z_s v$ the scalar matrix $\varpi_v\cdot 1$ for $v\in T$; and the analogous data $\varpi_K$, $n_K$, $r_K$, $z_K$ over $K$ — there exists a continuous linear functional $\Delta: C(X,\mathbb{C})\to\mathbb{C}$ such that:
--
--   — (no atomic mass) for every table $\tau$ of pairs of complex numbers indexed by the places of $K$ and every $\varepsilon>0$ there are sets $U_v$, open and containing $\tau_v$ for $v\in T$, such that every $g\in C(X,\mathbb{C})$ which vanishes at all $y\in X$ with $y_{w'v}\notin U_v$ for some $v\in T$ and satisfies $\|g\|\le1$ pointwise has $\|\Delta g\|<\varepsilon$;
--
--   — for all exponent functions $k$, $j$ on the places of $K$, every continuous compactly supported $\varphi_L$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ for which `IsSemiLocalFactorization K L (SK ∪ T) φL φa φf` holds with semi-local components given at $v\in T$ by the Hecke-word indicator sums $x\mapsto\sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf{1}_{\mathrm{semiLocalIntegralSet}}\bigl(c_v(\prod_m r_T v(\iota m)\cdot z_s v^{\,j_v})^{-1}x\bigr)$, where $c_v$ is the semi-local component of the local embedding at $\mathrm{ws}\,v$, and at $v\notin T$ by $\varphi_S v$, with $\varphi_L$ bi-invariant under `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` and arch-bi-finite for $\mathrm{tys}_L$; and for every family $\mathrm{fam}$ of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ indexed by the multi-exponents $m$ such that each $m$ in `SatakeCombination.slotIndex K L ws k j T` gives a function which is bi-invariant under `principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K`, arch-bi-finite for $\mathrm{tys}_K$, with $f_{a,K}$ an archimedean test factor and each $f_{S,K}v$ ($v\in S_K$) a local test function, and which factors as $\mathrm{fam}_m(g)=f_{a,K}(g_\infty)\cdot f\!f(g_{\mathrm{fin}})$ for some locally constant compactly supported $f\!f$ that equals, on elements all of whose components outside $S_K\cup T$ are integral, the product over $v\in S_K\cup T$ of the local factor (for $v\in T$ the Hecke-word indicator sum with exponents $m_v(0)$ and $m_v(1)$, otherwise $f_{S,K}v$) and vanishes when some component outside $S_K\cup T$ is non-integral; and such that $\varphi_L$ matches at $\sigma^{-1}$ over $S_K\cup T$ with $x\mapsto\sum_{m}\mathrm{slotFamilyCoeff}(m)\,\mathrm{fam}_m(x)$ — one has, for every $g\in C(X,\mathbb{C})$ given on $X$ by $g(x)=\prod_{v\in T}\bigl((x_{w'v})_1\bigr)^{k_v}\bigl(\mathrm{cNorm}(w'v)^{-1}(x_{w'v})_2\bigr)^{j_v}$:
--   $$\mathrm{intercept}\bigl(F_L\bigr)-[L:K]\,\lambda\sum_{\xi_K\in\Xi}\;\sum_{m}\mathrm{slotFamilyCoeff}(m)\,\mathrm{intercept}\bigl(F_{K,\xi_K,m}\bigr)=\Delta g,$$
--   the sums over $m$ running over `SatakeCombination.slotIndex K L ws k j T`. Here $\mathrm{intercept}(F)$ is the limit along $R\to\infty$ of $F(R)-R\cdot\mathrm{slope}(F)$ (a `limUnder`, with the slope functional of the same development); $F_L(R)$ is the integral over `canonicalTruncationDomain L α β` in $x$, and over $\Omega_L$ in $z$, of $\xi_L(z)$ times the difference of the twisted parabolic sum $\sum_\delta\varphi_L\bigl(x^{-1}\delta\,\sigma^{-1}_{\mathbb{A}}(z x)\bigr)$, over those $\delta\in\mathrm{GL}_2(L)$ whose twisted norm class is the conjugacy class of some $\gamma$ in the hyperbolic or unipotent cell of $\mathrm{GL}_2(K)$, and the indicator of the set where the adelic height of $L$ exceeds $e^{R}$, applied to the constant term — integration of the unipotent translates `unipotentGL2` against the conditional adelic additive Haar measure on `adelicBox L` coming from `productionPinsOf` — of the twisted adelic kernel $y\mapsto\sum_{\gamma\in\mathrm{GL}_2(L)}\varphi_L(x^{-1}\gamma\,\sigma^{-1}_{\mathbb{A}}y)$, evaluated at $z x$; and $F_{K,\xi_K,m}(R)$ is the analogous integral over `canonicalTruncationDomain K α β` and $\Omega_K$ of $\xi_K(z)$ times the difference of the hyperbolic and unipotent parts of the adelic kernel of $\mathrm{fam}_m$ and the corresponding truncating indicator applied to the constant term of the adelic kernel $y\mapsto\sum_{\gamma\in\mathrm{GL}_2(K)}\mathrm{fam}_m(x^{-1}\gamma y)$.
--
--   The constant $\lambda$ is quantified before $T$, so the same $\lambda$ serves for all admissible place sets $T$ and all the accompanying local data.
--
--   This is the parabolic (hyperbolic plus unipotent) half of Langlands' comparison of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over $L$ with the sum over the base-change fibre $\Xi$ of ordinary trace formulae over $K$, in the form of an identity between the intercepts of the truncated parabolic contributions along Hecke words at the places of $T$, with the discrepancy realised as a continuous linear functional on continuous functions on the compact set of Hecke tables that carries no atomic mass. It feeds the twisted geometric remainder statement [`AutomorphicForm.exists_continuous_noAtomicMass_twistedGeometricRemainder_sub_finrank_mul_const_mul_sum_eq`](thm.html#AutomorphicForm.exists_continuous_noAtomicMass_twistedGeometricRemainder_sub_finrank_mul_const_mul_sum_eq), from which the eigenvalue-by-eigenvalue comparison is extracted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform.lean

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
    AutomorphicForm.exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform
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
      AreMatchingAt K L σ.symm (SK ∪ T) φL
        (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x) →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
      HalfLine.intercept (fun R : ℝ =>
        ∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.hyperbolicCell K ∨ γ ∈ AutomorphicForm.unipotentCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y =>
                    AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φL x y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
        (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m *
            HalfLine.intercept (fun R : ℝ =>
              ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
                (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  ((AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                      AutomorphicForm.adelicKernelUnipotentPart K (fam m) x
                        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
                    Set.indicator
                      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                      (@AutomorphicForm.constantTerm _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                        (productionPinsOf K ΦK
                          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                        (fun t => AutomorphicForm.unipotentGL2 t)
                        (fun y => AutomorphicForm.adelicKernel K (fam m) x y))
                      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
                ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        Δ g := by sorry
