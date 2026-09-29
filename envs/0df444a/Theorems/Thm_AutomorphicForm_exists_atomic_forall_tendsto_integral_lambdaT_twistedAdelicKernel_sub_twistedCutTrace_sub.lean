-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub
-- name    : AutomorphicForm.exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/fb4c4dbc-7aaa-5a70-88ba-2387f5388582
-- title:
--   Atomic spectral data for the twisted truncated GL₂ trace
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ finite and Galois, $\mathbb{A}_L$ denotes the adele ring of $L$ and $\mathrm{GL}_2(\mathbb{A}_L)$ (written `AdelicGL2 (𝓞 L) L`) carries its Borel structure and Haar measure `adelicGLHaar`.
--
--   The data are: real numbers $\alpha<\beta$ with $0<\alpha$; a set $\Phi_L\subseteq\mathrm{GL}_2(\mathbb{A}_L)$; a Haar measure $\nu_{Z_L}$ on $\mathbb{A}_L^\times$ and a set $\Omega_L\subseteq\mathbb{A}_L^\times$; a datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism $\mathrm{Gal}(L/K)\to\mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ whose automorphisms are continuous and extend the action on $L$; an element $\sigma\in\mathrm{Gal}(L/K)$; a finite set $S_L$ of finite places of $L$; a homomorphism $\xi_L$ from the top subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$; an ideal $N\subseteq\mathcal{O}_L$; an archimedean type family $\mathrm{tys}_L$ for $L$ (for each infinite place a finite list of types, each a representation of `rowIsometrySubgroup₀` of the completion on some $\mathbb{C}^n$); a finite set $S$ of finite places of $K$; test-function factors $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$ and $\varphi_S(v)$ on $\mathrm{GL}_2(L\otimes_K K_v)$ for each finite place $v$ of $K$; a set $X$ of *tables*, i.e. of functions from the finite places of $L$ to $\mathbb{C}\times\mathbb{C}$; real numbers $c,u,d_1,d_2$ with $c>0$; a set $T_c\subseteq\mathrm{GL}_2(\mathbb{A}_L)$; and a set $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_L)$.
--
--   The hypotheses fall into the following groups. *Determinant slab and fundamental domains*: `hΦs` puts $\Phi_L$ inside the slab $\{g:\ \|\det g\|_{\mathbb{A}_L}\in[\alpha,\beta]\}$, where $\|\cdot\|$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the module of the idele acting on $\mathbb{A}_L$; `hΦ` makes $\Phi_L$ a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` with respect to Haar measure restricted to that slab; `hΩL` makes $\Omega_L$ a fundamental domain for the image of $L^\times$ in $\mathbb{A}_L^\times$ with respect to $\nu_{Z_L}$. *Cyclicity*: `hgen` asserts that every element of $\mathrm{Gal}(L/K)$ is an integral power of $\sigma$. *Places and character*: `hSL` says that $S_L$ is a union of fibres, two finite places of $L$ over the same place of $K$ lying in $S_L$ together or not at all; `hξc` asserts continuity of $z\mapsto\xi_L(z)$ on $\mathbb{A}_L^\times$ and `hξt` its triviality on the image of $L^\times$; `hN` requires every finite place of $L$ whose prime divides $N$ to lie in $S_L$. *Table box*: `hX` requires $X$ to contain every table $x$ such that $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$, writing $\pi_w=\xi_L(\det \mathrm{heckeGen}_w)$, one has $(x_w)_2=\mathrm{N}(w)\,\pi_w$ with $\mathrm{N}(w)$ the absolute norm of $w$, $\|(x_w)_1\|\le(\mathrm{N}(w)+1)\sqrt{\|\pi_w\|}$, and $\overline{(x_w)_1}=\bigl(\overline{(x_w)_2}/\|(x_w)_2\|\bigr)(x_w)_1$. *Siegel confinement of $\Phi_0$*: `hTc` asserts compactness of $T_c$; `hΦ₀S` puts $\Phi_0$ into the union over $y\in T_c$ of the right translates by $y$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` (finite part integral, all local heights $\ge c$, all window quantities $\le u^2$, all archimedean determinant norms in $[d_1,d_2]$); `hΦ₀s` puts $\Phi_0$ into the same determinant slab and `hΦ₀` makes it, too, a fundamental domain for $\mathrm{GL}_2(L)$ with respect to the restricted Haar measure.
--
--   The conclusion asserts the existence of a sequence of tables $t_n\in X$ ($n\in\mathbb{N}$), with membership witnesses `htabs`, and of complex numbers $c_n$, such that three things hold.
--
--   First, $\sum_n\|c_n\|<\infty$.
--
--   Second, every index $n$ with $c_n\ne0$ satisfies: (a) $t_n$ is constant on fibres outside $S_L$, i.e. $t_n(w)=t_n(w')$ whenever $w,w'\notin S_L$ lie over the same place of $K$; and (b) there are a nonzero ideal $M\subseteq\mathcal{O}_L$ and homomorphisms $\chi_1,\chi_2:\mathbb{A}_L^\times\to\mathbb{C}^\times$, each continuous as a $\mathbb{C}$-valued function and each trivial on the image of $L^\times$, such that for every $w\notin S_L$ the pair $t_n(w)$ is the pair of $w$-th entries $(a_w,b_w)$ of the Eisenstein Hecke eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), whose entries are $a_w=\chi_1(\varpi_w)+\chi_2(\varpi_w)$ and $b_w=\chi_1(\varpi_w)\chi_2(\varpi_w)$ for the uniformizer idele at $w$, and whose level is $M$.
--
--   Third, for every finite set $T$ of finite places of $K$ disjoint from $S$ with $\#T\ge2$ and such that no place of $L$ above a place of $T$ lies in $S_L$; for every choice of an extension $w_v$ of each place $v$ of $K$ to $L$, and of places $w'_v$ of $L$ with $(w'_v)$'s prime ideal equal to the $\sigma^{-1}$-translate of that of $w_v$ for $v\in T$; for every family $\varpi_v$ of elements of the valuation ring of $L_{w_v}$ that are irreducible for $v\in T$ and whose images in $L_{w_v}$ are nonzero for $v\in T$; for every family of natural numbers $n_v$ and of elements $r_{v,i}\in\mathrm{GL}_2(L_{w_v})$ ($i\in\mathrm{Fin}\,n_v$) such that for each $v\in T$ the family $(r_{v,i})_i$ is a Hecke coset system (in the sense of [`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15): the $r_{v,i}$ lie in the double coset of $\mathrm{diag}(\varpi_v,1)$ under the integral subgroup $\mathrm{GL}_2(\mathcal{O}_{w_v})$, they cover that double coset modulo the integral subgroup on the right, and they are pairwise distinct modulo it); and for every family $z_v\in\mathrm{GL}_2(L_{w_v})$ with $z_v=\varpi_v\cdot 1$ for $v\in T$: there exist continuous linear functionals $\mu,\nu:C(X,\mathbb{C})\to\mathbb{C}$ with the following two properties.
--
--   (i) *Diffuseness of $\mu$ at the places $w'_v$*: for every $\tau$ assigning to each place of $K$ a point of $\mathbb{C}\times\mathbb{C}$ and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb{C}\times\mathbb{C}$, open and containing $\tau_v$ for every $v\in T$, such that $\|\mu(g)\|<\varepsilon$ for every $g\in C(X,\mathbb{C})$ bounded by $1$ in absolute value which vanishes at every table $y\in X$ with $y(w'_v)\notin U_v$ for some $v\in T$.
--
--   (ii) *Asymptotic trace identity*: for all families of natural numbers $k_v,j_v$, every continuous compactly supported $\varphi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` holds for the local family which equals $\varphi_S(v)$ for $v\notin T$ and, for $v\in T$, equals
--   $$x\mapsto\sum_{\iota:\mathrm{Fin}\,k_v\to\mathrm{Fin}\,n_v}\mathbf{1}_{\mathrm{semiLocalIntegralSet}}\Bigl(\bigl(\mathrm{semiLocalComponent}_v(\mathrm{localEmbed}_{w_v}(r_{v,\iota(0)}\cdots r_{v,\iota(k_v-1)}\,z_v^{\,j_v}))\bigr)^{-1}x\Bigr),$$
--   the Hecke word of length $k_v$ in the coset representatives twisted by the $j_v$-th power of the central element (that is: $\varphi_a$ is archimedean-smooth of compact support, $\varphi_f$ is locally constant of compact support, each local factor at a place of $S\cup T$ is locally constant of compact support, $\varphi_f$ is the product of the local factors on elements integral outside $S\cup T$ and vanishes on elements not integral at some place outside $S\cup T$, and $\varphi$ factors as $\varphi_a$ on the archimedean part times $\varphi_f$ on the finite part), and such that $\varphi$ is bi-invariant under the intersection of the level-$N$ subgroup `levelOne (𝓞 L) L N` with the kernel of the archimedean projection, and satisfies `IsArchBiFinite L tysL φ` (the function $g\mapsto\varphi(g^{-1})$ lies in the archimedean cut submodule of type $\mathrm{tys}_L$ and $\varphi$ lies in the dual cut submodule): for every $g\in C(X,\mathbb{C})$ which on $X$ is given by the Hecke monomial
--   $$g(x)=\prod_{v\in T}\bigl(x(w'_v)\bigr)_1^{k_v}\Bigl(\mathrm{N}(w'_v)^{-1}\bigl(x(w'_v)\bigr)_2\Bigr)^{j_v},$$
--   the function of $R\in\mathbb{R}$ given by the difference of
--   $$\int_{\Phi_0}\int_{\Omega_L}\xi_L(z)\,\bigl(\lambda^{e^R}K_\varphi(x,\cdot)\bigr)\bigl(\mathrm{centralScalar}(z)\,x\bigr)\,d\nu_{Z_L}(z)\,d\,\mathrm{adelicGLHaar}(x)$$
--   and
--   $$\nu_{Z_L}\bigl(\Omega_L\cap\{z:\|\det \mathrm{centralScalar}(z)\|_{\mathbb{A}_L}\in[\alpha,\beta]\}\bigr)\cdot\sum_{\Psi}\mathrm{twistedCutTrace}(\Psi)\;+\;R\,\nu(g)+\sum_n c_n\,g(t_n)+\mu(g)$$
--   tends to $0$ as $R\to+\infty$. Here $K_\varphi(x,y)=\sum_{\gamma\in\mathrm{GL}_2(L)}\varphi\bigl(x^{-1}\gamma\,\sigma^{-1}(y)\bigr)$ is `twistedAdelicKernel` for the adelic action `sigmaAdelicAct K L D σ.symm` of $\sigma^{-1}$ obtained from $D$; $\lambda^{T}f(g)=f(g)-\mathbf{1}_{\{\mathrm{adelicHeight}>T\}}(g)\,(\text{constant term of }f\text{ along }t\mapsto\left(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\right))(g)$, the constant term being taken with respect to the measure of the carrier record `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (heckeGen) (adelicBox L)`, namely additive Haar measure on $\mathbb{A}_L$ conditioned on the adelic box, and the height being [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158); the sum over $\Psi$ runs over the subtype of Hecke eigensystems in `cuspClasses` for that same record, $\xi_L$, $N$ and $S_L$, i.e. those of level $N$ whose $a$- and $b$-entries vanish on $S_L$ and whose isotypic cusp submodule is nonzero, and its terms are $\mathrm{twistedCutTrace}(\Psi)=$ `twistedCutTrace K L D σ ... Ψ tysL φ hφ hφc`, the trace of the $\sigma$-twisted convolution operator by $\varphi$ on the intersection of the isotypic cusp submodule of $\Psi$ with the archimedean cut submodule of type $\mathrm{tys}_L$, taken to be $0$ if that operator fails to preserve the space; the volume factor and the sum are read in $\mathbb{C}$.
--
--   No condition beyond continuity and linearity is imposed on $\nu$, whose contribution enters with the factor $R$; the tables $t_n$ and the coefficients $c_n$ are chosen before, and hence uniformly in, $T$ and all the local Hecke data.
--
--   This is the spectral side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$, evaluated along Hecke words at two or more places of $K$ outside the ramification set: the truncated twisted kernel integrated over a Siegel-confined fundamental domain is compared, as the truncation parameter grows, with the twisted cuspidal trace plus a term linear in the parameter, an absolutely convergent atomic part supported on Eisenstein tables, and a diffuse remainder. It is used by the unramified variant of the same asymptotic statement, which feeds the comparison of twisted traces with base-change data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub
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
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ))
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
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
      ∃ μ ν : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖μ g‖ < ε) ∧
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
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
    Filter.Tendsto (fun R : ℝ =>
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φ x y)
            (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
      ((((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                    (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                    Ψ ∈ cuspClasses L
                      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                  twistedCutTrace K L D σ
                    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc) +
            ((R : ℂ) * ν g + (∑' n, cs n * g ⟨tabs n, htabs n⟩) + μ g)))
      Filter.atTop (nhds 0) := by sorry
