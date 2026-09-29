-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram
-- name    : AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/e8acedb6-d55e-587a-b70b-6e69ce205c5b
-- title:
--   Twisted GL₂ trace identity with atom-free remainder functional
-- statement:
--   Throughout, $K$ and $L$ are number fields, $L$ a finite Galois extension of $K$.
--
--   **Truncation slab and global fundamental domain.** Real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_L\subseteq \mathrm{GL}_2(\mathbb{A}_L)$ (the abbreviation `AdelicGL2 (𝓞 L) L`) which by `hΦs` is contained in the slab $\{g:\ \|\det g\|_{\mathbb{A}_L}\in[\alpha,\beta]\}$, where $\|\cdot\|_{\mathbb{A}_L}$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the modulus `distribHaarChar` of multiplication on the adeles; by `hΦ`, $\Phi_L$ is a fundamental domain for the range of `globalPoints (𝓞 L) L` (the image of $\mathrm{GL}_2(L)$ in $\mathrm{GL}_2(\mathbb{A}_L)$ under the structure map) with respect to the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` restricted to that slab.
--
--   **Centre.** A measurable and Borel structure on the idele group $(\mathbb{A}_L)^\times$, a Haar measure $\nu_{Z_L}$ on it, and a set $\Omega_L$ which by `hΩL` is a fundamental domain for the image of $L^\times$ in $(\mathbb{A}_L)^\times$ with respect to $\nu_{Z_L}$.
--
--   **Galois descent and cyclicity.** A datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, compatible with the embedding of $L$ and continuous in each Galois element; an element $\sigma\in\mathrm{Gal}(L/K)$ such that, by `hgen`, every $\tau\in\mathrm{Gal}(L/K)$ is an integral power of $\sigma^{-1}$.
--
--   **Excluded places.** A finite set $S_L$ of primes of $\mathcal{O}_L$ such that membership in $S_L$ depends only on the prime of $\mathcal{O}_K$ below (`hSL`), and such that every $w$ with $\mathrm{ramificationIdx}'\neq 1$ over the prime beneath it lies in $S_L$ (`hSLram`).
--
--   **Central character.** A homomorphism $\xi_L$ from the full subgroup $\top\le(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the image of $L^\times$ (`hξt`), and such that $\xi_L(\det\,\mathrm{heckeGen}_w)=\xi_L(\det\,\mathrm{heckeGen}_{w'})$ whenever $w,w'\notin S_L$ lie over the same prime of $\mathcal{O}_K$ (`hξσ`), where `heckeGen (𝓞 L) L w` is the adelic Hecke generator at $w$ attached to the chosen uniformiser.
--
--   **Level.** An ideal $N\subseteq\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`).
--
--   **Archimedean and test-function data.** An archimedean type family $\mathrm{tys}_L$ (for each infinite place of $L$ a finite list of archimedean representation types); a finite set $S$ of primes of $\mathcal{O}_K$; a function $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$; for each prime $v$ of $\mathcal{O}_K$ a function $\varphi_S(v)$ on $\mathrm{GL}_2(L\otimes_K K_v)$.
--
--   **Table space.** A compact set $X$ of "tables", i.e. functions from the primes of $\mathcal{O}_L$ to $\mathbb{C}\times\mathbb{C}$, which by `hX` contains every table $x$ with $x_w=0$ for all $w\in S_L$ and, for all $w\notin S_L$: second coordinate $(x_w)_2=\mathrm{cNorm}(w)\,\xi_L(\det\,\mathrm{heckeGen}_w)$ with $\mathrm{cNorm}(w)=|\mathcal{O}_L/w|$; first coordinate bounded by $\|(x_w)_1\|\le(|\mathcal{O}_L/w|+1)\sqrt{\|\xi_L(\det\,\mathrm{heckeGen}_w)\|}$; and $\overline{(x_w)_1}=\bigl(\overline{(x_w)_2}/\|(x_w)_2\|\bigr)(x_w)_1$.
--
--   **Conclusion.** Two assertions hold.
--
--   First, the real number $\nu_{Z_L}\bigl(\Omega_L\cap\{z:\ \|\det(\mathrm{diag}(z,z))\|_{\mathbb{A}_L}\in[\alpha,\beta]\}\bigr)$, viewed in $\mathbb{C}$, is non-zero; here $\mathrm{diag}(z,z)$ is `centralScalar (𝓞 L) L z`. Call this number the band constant.
--
--   Second, there exist tables $t_n\in X$ ($n\in\mathbb{N}$), with the membership witnesses $\mathrm{htabs}$, and complex coefficients $c_n$ such that $\sum_n\|c_n\|<\infty$ and the following two further properties hold.
--
--   (a) *Eisenstein shape of the atoms.* For every $n$ with $c_n\neq 0$: the table $t_n$ takes one and the same value at any two primes $w,w'\notin S_L$ lying over the same prime of $\mathcal{O}_K$; and there are a non-zero ideal $M\subseteq\mathcal{O}_L$ and homomorphisms $\chi_1,\chi_2:(\mathbb{A}_L)^\times\to\mathbb{C}^\times$, each continuous as a $\mathbb{C}$-valued function and trivial on the image of $L^\times$, such that for every $w\notin S_L$ the value $t_n(w)$ is the pair $\bigl(a_w,b_w\bigr)$ of the Hecke eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), whose level is $M$ and whose entries at $w$ are $a_w=\chi_1(\varpi_w)+\chi_2(\varpi_w)$ and $b_w=\chi_1(\varpi_w)\chi_2(\varpi_w)$, with $\varpi_w$ the uniformiser idele at $w$.
--
--   (b) *The trace identity.* For every finite set $T$ of primes of $\mathcal{O}_K$ disjoint from $S$, with $|T|\ge 2$, such that no prime of $\mathcal{O}_L$ over a member of $T$ lies in $S_L$; for every choice $\mathrm{ws}$ of an extension $w\mid v$ to $\mathcal{O}_L$ for each $v$, and every map $w'$ from primes of $\mathcal{O}_K$ to primes of $\mathcal{O}_L$ with $(w'v)=\sigma^{-1}\cdot(\mathrm{ws}\,v)$ as ideals for $v\in T$; for every family $\varpi$ with $\varpi_v$ in the valuation ring of $L$ at $\mathrm{ws}\,v$, irreducible for $v\in T$ and with non-zero image in the completion (the witness $h\varpi_{s0}$); for every family $n_v\in\mathbb{N}$ and every family $r_{T,v}:\mathrm{Fin}(n_v)\to \mathrm{GL}_2(L_{\mathrm{ws}\,v})$ which for $v\in T$ is a Hecke coset system in the sense of [`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15) for the integral subgroup $\mathrm{GL}_2(\mathcal{O}_{\mathrm{ws}\,v})$ and the element $\mathrm{diag}(\varpi_v,1)$ (the representatives lie in the double coset, exhaust its left cosets, and are pairwise distinct modulo the subgroup); and for every family $z_v\in\mathrm{GL}_2(L_{\mathrm{ws}\,v})$ which for $v\in T$ is the scalar matrix $\varpi_v\cdot 1$ — there exists a continuous $\mathbb{C}$-linear functional $\Lambda$ on $C(X,\mathbb{C})$ with the three properties below.
--
--   (b1) *No atomic mass in the $T$-coordinates.* For every $\tau$ assigning to each prime of $\mathcal{O}_K$ a pair of complex numbers and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb{C}\times\mathbb{C}$ with $U_v$ open and $\tau_v\in U_v$ for all $v\in T$, such that every $g\in C(X,\mathbb{C})$ which vanishes at each $y\in X$ for which $y(w'v)\notin U_v$ for some $v\in T$, and which satisfies $\|g(y)\|\le 1$ everywhere, has $\|\Lambda g\|<\varepsilon$.
--
--   (b2) *Support on fibre-constant tables.* $\Lambda g=0$ for every $g\in C(X,\mathbb{C})$ vanishing at every $y\in X$ whose values agree at any two primes $w_1,w_2\notin S_L$ lying over the same prime of $\mathcal{O}_K$.
--
--   (b3) *The identity itself.* For all families $k_v,j_v\in\mathbb{N}$, every continuous compactly supported $\varphi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` holds for the semi-local factors which at $v\in T$ are the function
--   $$x\mapsto\sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf 1_{\mathrm{semiLocalIntegralSet}}\Bigl(\bigl(\mathrm{semiLocalComponent}_v(\mathrm{localEmbed}_{\mathrm{ws}\,v}(r_{T,v}(\iota_0)\cdots r_{T,v}(\iota_{k_v-1})\,z_v^{\,j_v}))\bigr)^{-1}x\Bigr)$$
--   and at $v\notin T$ are $\varphi_S(v)$ — the factorisation hypothesis requiring that $\varphi_a$ be a smooth compactly supported function of the archimedean matrix entries, $\varphi_f$ locally constant with compact support, each prescribed factor at $v\in S\cup T$ locally constant with compact support, $\varphi_f(h)$ equal to the product of these factors when all semi-local components outside $S\cup T$ are integral and $0$ otherwise, and $\varphi$ the product of $\varphi_a$ on the archimedean part with $\varphi_f$ on the finite part — and such that $\varphi$ is bi-invariant under `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` and satisfies `IsArchBiFinite L tysL φ` (both $g\mapsto\varphi(g^{-1})$ and $\varphi$ lie in the archimedean cut, respectively dual cut, submodules determined by $\mathrm{tys}_L$): for every $g\in C(X,\mathbb{C})$ given on $X$ by
--   $$g(x)=\prod_{v\in T}\bigl(x(w'v)\bigr)_1^{\,k_v}\bigl(\mathrm{cNorm}(w'v)^{-1}\,(x(w'v))_2\bigr)^{\,j_v},$$
--   one has the equality of the following two complex numbers.
--
--   The left-hand side is
--   $$\int_{\Phi_L}\int_{\Omega_L}\xi_L(z)\sum_{\delta}\varphi\bigl(x^{-1}\,\delta\,{}^{\sigma^{-1}}(\mathrm{diag}(z,z)\,x)\bigr)\,d\nu_{Z_L}\,d\,\mathrm{adelicGLHaar}$$
--   minus the band constant times $\sum_{\Psi}\mathrm{twistedCutTrace}$, where: the inner sum is the `finsum` over those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted conjugacy class has norm class (under [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766)) equal to the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ which is elliptic (its characteristic polynomial has no root in $K$) or central (a scalar matrix); $\delta$ is sent into $\mathrm{GL}_2(\mathbb{A}_L)$ by `globalPoints`, and ${}^{\sigma^{-1}}(\cdot)$ denotes `sigmaAdelicAct K L D σ.symm`; and the spectral sum runs over the subtype of Hecke eigensystems $\Psi$ over $\mathbb{C}$ for $L$ lying in `cuspClasses L pins ξL N SL` — i.e. with $\Psi.\mathrm{level}=N$, $\Psi.a_w=\Psi.b_w=0$ for $w\in S_L$, and non-zero isotypic cusp submodule — each term being `twistedCutTrace K L D σ pins ξL N SL Ψ tysL φ` with the stated continuity and compact-support witnesses, that is the twisted convolution trace of $\varphi$ along $\sigma$ on the intersection of the $\Psi$-isotypic cusp submodule with the archimedean cut submodule; here $\mathrm{pins}$ is `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, whose measure data are the adelic Haar measure on $\mathrm{GL}_2$, the subgroup $\top$ of the ideles, and the additive adelic Haar measure conditioned on the adelic box.
--
--   The right-hand side is
--   $$\sum_{n}c_n\,g(t_n)\;+\;\Lambda g\;-\;\mathrm{twistedGeometricRemainder}\bigl(K,L,D,\sigma^{-1},\mathrm{hgen},\Phi_L,\Phi_0,\nu_{Z_L},\Omega_L,\xi_L,\varphi\bigr),$$
--   with $\Phi_0=$ [`AutomorphicForm.canonicalTruncationDomain L α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32); the remainder is the half-line intercept, as $R\to\infty$, of the difference between the corresponding $\Omega_L$-averaged integral over $\Phi_0$ of the truncation $\lambda_{e^R}$ of the twisted adelic kernel of $\varphi$ and the same elliptic-plus-central geometric term integrated over $\Phi_L$.
--
--   This is the unramified-place form of the twisted (base-change) trace identity for $\mathrm{GL}_2$ over a cyclic extension $L/K$: the geometric side restricted to elliptic and central twisted classes, minus the cuspidal twisted trace, is expressed as an absolutely convergent sum of Eisenstein atoms, a distribution $\Lambda$ with no atomic mass in the $T$-coordinates and supported on fibre-constant Hecke tables, and the twisted geometric remainder attached to the canonical truncation domain. It is the input to the subsequent comparison of Hecke-word sums of twisted and untwisted cut traces and to the fibre-sum identity for central-elliptic classes at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram.lean

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
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain

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
    AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram
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
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hSLram : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
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
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X) :
    ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) ≠ 0 ∧
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tabs n w = tabs n w') ∧
      ∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₂ z = 1) ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
          tabs n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
            (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
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
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      (∀ g : C(X, ℂ),
        (∀ y : X, (∀ w₁ w₂ : HeightOneSpectrum (𝓞 L), w₁ ∉ SL → w₂ ∉ SL →
            HeightOneSpectrum.under (𝓞 K) w₁ = HeightOneSpectrum.under (𝓞 K) w₂ →
              (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w₁ = (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) w₂) →
            g y = 0) →
        Λ g = 0) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) → (
  ∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
          ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
          ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
              Ψ ∈ cuspClasses L
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
            twistedCutTrace K L D σ
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc =
          ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g -
            AutomorphicForm.twistedGeometricRemainder K L D σ.symm hgen ΦL
              (AutomorphicForm.canonicalTruncationDomain L α β) νZL ΩL ξL φ) := by sorry
