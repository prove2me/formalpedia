-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_sub_lambdaT_tsum_finsum_twistedConvOp_sub_lambdaT_finsum_twistedConvOp_chiDet_sub
-- name    : AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_sub_lambdaT_tsum_finsum_twistedConvOp_sub_lambdaT_finsum_twistedConvOp_chiDet_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/94171cad-7cbb-5dcc-8d4d-88e5b10a1b8b
-- title:
--   Continuous block of the σ-twisted spectral side along Hecke words
-- statement:
--   Throughout, $L/K$ is a finite Galois extension of number fields, $\mathbb A=\mathbb A_L$ is the adele ring of $L$, $G=\mathrm{GL}_2(\mathbb A)$ (the type `AdelicGL2 (𝓞 L) L`), and `adelicGLHaar (Fin 2) (𝓞 L) L` is the Haar measure on $G$ for the Borel structure `glBorel`. For an idele $z$, $\|z\|$ denotes [`NumberField.TateGlobal.ideleNorm L z`](def/NumberField_TateGlobalZeta.html#L19), the distributive Haar character of multiplication by $z$ on $\mathbb A$; the *slab* is the set of $g\in G$ with $\|\det g\|\in[\alpha,\beta]$.
--
--   **Slab and fundamental domain for $\mathrm{GL}_2(L)$.** Reals $0<\alpha<\beta$ are given (`hα`, `hαβ`), together with a set $\Phi_L\subseteq G$ contained in the slab (`hΦs`) which is a fundamental domain for the image of $\mathrm{GL}_2(L)$ in $G$ under `globalPoints`, with respect to `adelicGLHaar` restricted to the slab (`hΦ`).
--
--   **Centre.** A Haar measure $\nu_{Z}$ on $\mathbb A^\times$ is given, together with a set $\Omega_L\subseteq\mathbb A^\times$ which is a fundamental domain for the image of $L^\times$ in $\mathbb A^\times$ with respect to $\nu_Z$ (`hΩL`).
--
--   **Galois descent and cyclicity.** $D$ is an `IdeleGaloisDescent (𝓞 L) K L`, i.e. a homomorphism $\tau\mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb A$, compatible with the structure map $L\to\mathbb A$ and continuous in each $\tau$; $\sigma\in\mathrm{Gal}(L/K)$ satisfies `hgen`: every $\tau$ lies in the subgroup of integral powers of $\sigma$. Write $\sigma_{\mathbb A}^{\pm1}$ for the automorphism `sigmaAdelicAct K L D` of $G$ induced entrywise by $D.\mathrm{act}$ applied to $\sigma$ or $\sigma^{-1}$.
--
--   **Character, bad set, level, archimedean types.** $S_L$ is a finite set of finite places of $L$ which is a union of fibres over $K$ (`hSL`: $w\in S_L\iff w'\in S_L$ whenever $w,w'$ lie over the same place of $K$); $\xi_L$ is a homomorphism from the top subgroup of $\mathbb A^\times$ to $\mathbb C^\times$, continuous (`hξc`) and trivial on the principal ideles (`hξt`); $N$ is an ideal of $\mathcal O_L$ all of whose prime divisors lie in $S_L$ (`hN`); $\mathrm{tys}_L$ is an `ArchTypeFamily L`, assigning to each infinite place $w$ a finite family of representations of the local row-isometry group.
--
--   **Semi-local test data and the table space.** $S$ is a finite set of finite places of $K$; $\varphi_a$ is a function on $\mathrm{GL}_2$ of the infinite adeles of $L$ and $\varphi_S$ assigns to each finite place $v$ of $K$ a function on $\mathrm{GL}_2(L\otimes_K K_v)$. $X$ is a set of *tables*, i.e. of functions $x$ from the finite places of $L$ to $\mathbb C\times\mathbb C$, and `hX` requires $X$ to contain every table $x$ such that $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$, writing $\xi_w=\xi_L(\det \mathrm{heckeGen}(w))$: $(x_w)_2=\mathrm{Nm}(w)\,\xi_w$ with $\mathrm{Nm}(w)=$ `HeckeEigensystem.cNorm w` the absolute norm of $w$, $\|(x_w)_1\|\le(\mathrm{Nm}(w)+1)\sqrt{\|\xi_w\|}$, and $\overline{(x_w)_1}=\bigl(\overline{(x_w)_2}/\|(x_w)_2\|\bigr)(x_w)_1$.
--
--   **Siegel fundamental domain $\Phi_0$.** Reals $c,u,d_1,d_2$ with $0<c$ (`hc`), a compact set $T_c\subseteq G$ and a set $\Phi_0\subseteq G$ are given with: $\Phi_0\subseteq\bigcup_{y\in T_c}(\cdot\,y)\bigl[\mathrm{centreCutSiegelSet}\,L\,c\,u\,d_1\,d_2\bigr]$ (`hΦ₀S`), where the centre-cut Siegel set consists of those $g$ whose finite part is integral and which at every infinite place $w$ satisfy $\mathrm{localHeight}\ge c$, $\mathrm{xWindowSq}\le u^2$ and $\mathrm{archDetNorm}_w\in[d_1,d_2]$; $\Phi_0$ lies in the slab (`hΦ₀s`) and is again a fundamental domain for $\mathrm{GL}_2(L)$ for `adelicGLHaar` restricted to the slab (`hΦ₀`).
--
--   **The orthonormal cuspidal system.** Let `pins` be `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L) (adelicBox L)`: the carrier data with measure `adelicGLHaar` on $G$, fundamental domain $\Phi_L$, central subgroup $\top$, level subgroups $U(M)=\mathrm{levelOne}(M)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}(w)$, and, on $\mathbb A$, the conditional probability measure $\nu$ obtained from the adelic additive Haar measure by conditioning on `adelicBox L`. A type $\iota$, functions $b:\iota\to(G\to\mathbb C)$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem L ℂ` are given with: `hb`, each $\mathrm{cls}(i)$ is a cuspidal class for `pins`, $\xi_L$, $N$, $S_L$ (level $N$, vanishing $a$- and $b$-entries on $S_L$, nonzero isotypic cusp space) and $b_i$ lies in the isotypic cusp submodule of $\mathrm{cls}(i)$ intersected with the archimedean cut submodule $\bigsqcap_w\bigsqcup_i$ `archTypeSubmoduleAt` of $\mathrm{tys}_L$; `hb₁`, $\int_{\Phi_L}b_i\overline{b_i}\,d\,$`adelicGLHaar`$=1$; `hb₀`, $\int_{\Phi_L}b_i\overline{b_j}=0$ for $i\ne j$; `hbs`, for every cuspidal class $\pi$ the set $\{i:\mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb C$-span of its $b$-images is exactly the cut isotypic submodule of $\pi$; `hbc` (completeness), every $\psi:G\to\mathbb C$ which is a smooth cusp automorphic function for `pins` and $\xi_L$, is continuous, is right invariant under $U(N)$, lies in the archimedean cut submodule and is orthogonal to all $b_i$ over $\Phi_L$, vanishes almost everywhere on $\Phi_L$.
--
--   **Conclusion.** There exist a sequence of tables $\mathrm{tabs}:\mathbb N\to(\text{places of }L\to\mathbb C\times\mathbb C)$ with $\mathrm{tabs}_n\in X$ for all $n$, and coefficients $\mathrm{cs}:\mathbb N\to\mathbb C$, such that the following three assertions hold.
--
--   (1) $\sum_n\|\mathrm{cs}_n\|<\infty$.
--
--   (2) For every $n$ with $\mathrm{cs}_n\ne0$: first, $\mathrm{tabs}_n$ is constant on fibres over $K$ outside $S_L$, that is $\mathrm{tabs}_n(w)=\mathrm{tabs}_n(w')$ whenever $w,w'\notin S_L$ lie over the same place of $K$; second, there are a nonzero ideal $M$ of $\mathcal O_L$ and two homomorphisms $\chi_1,\chi_2:\mathbb A^\times\to\mathbb C^\times$, each continuous and trivial on the principal ideles, such that for all $w\notin S_L$ the pair $\mathrm{tabs}_n(w)$ equals the pair of $a$- and $b$-entries at $w$ of the Eisenstein eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), namely $\bigl(\chi_1(\varpi_w)+\chi_2(\varpi_w),\,\chi_1(\varpi_w)\chi_2(\varpi_w)\bigr)$ with $\varpi_w=$ `uniformizerIdele L w`.
--
--   (3) For every finite set $T$ of finite places of $K$ which is disjoint from $S$, has at least two elements, and is such that no place of $L$ above a member of $T$ lies in $S_L$; for every choice of: extensions $w_v\in$ `v.Extension (𝓞 L)` for all $v$, a map $w'$ from places of $K$ to places of $L$ with $(w'_v)=\sigma^{-1}\cdot w_v$ as ideals for $v\in T$, uniformisers $\varpi_v$ in the valuation ring of the completion of $L$ at $w_v$ which are irreducible for $v\in T$ and have nonzero image in the completion (`hϖs0`), natural numbers $n_v$ and families $r_{T,v}:\mathrm{Fin}(n_v)\to\mathrm{GL}_2(L_{w_v})$ which for $v\in T$ form a Hecke coset system (`IsHeckeCosetSystem`) for the integral subgroup $\mathrm{GL}_2(\mathcal O_{w_v})$ and the element $\mathrm{diag}(\varpi_v,1)$, and elements $z_v\in\mathrm{GL}_2(L_{w_v})$ equal to the scalar matrix $\varpi_v\cdot 1$ for $v\in T$: there exist two continuous $\mathbb C$-linear functionals $\mu,\nu$ on $C(X,\mathbb C)$ with the following two properties.
--
--   (3a) (No point masses for $\mu$.) For every $\tau$ assigning to each place of $K$ a point of $\mathbb C\times\mathbb C$ and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb C\times\mathbb C$ with $U_v$ open and $\tau_v\in U_v$ for all $v\in T$, such that every $g\in C(X,\mathbb C)$ which vanishes at every table $y\in X$ admitting some $v\in T$ with $y(w'_v)\notin U_v$, and which satisfies $\|g(y)\|\le1$ everywhere, has $\|\mu(g)\|<\varepsilon$.
--
--   (3b) For all families of exponents $k_v,j_v\in\mathbb N$; for every continuous, compactly supported $\varphi:G\to\mathbb C$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles such that `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` holds for the semi-local family which at $v\in T$ is the Hecke-word function
--   $$x\mapsto\sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf 1_{\mathcal K_v}\Bigl(\bigl(\text{semiLocalComponent}_v(\mathrm{localEmbed}_{w_v}(r_{T,v}(\iota_0)\cdots r_{T,v}(\iota_{k_v-1})\,z_v^{\,j_v}))\bigr)^{-1}x\Bigr),$$
--   with $\mathcal K_v=$ `semiLocalIntegralSet K L v`, and at $v\notin T$ is $\varphi_S(v)$ — the factorisation asserting that $\varphi_a$ is an archimedean test factor, $\varphi_f$ a finite test factor, each component at a place of $S\cup T$ locally constant with compact support, $\varphi_f(h)=\prod_{v\in S\cup T}$ (component at $v$) whenever all semi-local components off $S\cup T$ are integral, $\varphi_f(h)=0$ otherwise, and $\varphi(g)=\varphi_a(\mathrm{glArch}\,g)\varphi_f(\mathrm{glFin}\,g)$ — and such that $\varphi$ is bi-invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$ and satisfies `IsArchBiFinite L tysL φ` (that is, $g\mapsto\varphi(g^{-1})$ lies in the archimedean cut submodule of $\mathrm{tys}_L$ and $\varphi$ lies in the dual cut submodule); and for every $g\in C(X,\mathbb C)$ given by
--   $$g(x)=\prod_{v\in T}\bigl(x(w'_v)\bigr)_1^{\,k_v}\,\Bigl(\mathrm{Nm}(w'_v)^{-1}\bigl(x(w'_v)\bigr)_2\Bigr)^{j_v}:$$
--   the following three statements hold. Here, for a parameter $R\in\mathbb R$, let $F_R(x)$ denote the value at $x$ of the truncation $\lambda^{e^R}$ — the operator `lambdaT` for the measure $\nu$ of `pins` on $\mathbb A$, the unipotent embedding $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$, the height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) and the threshold $e^R$, i.e. subtraction of the indicator of $\{\text{height}>e^R\}$ times the constant term — applied in the second variable and evaluated at the first, of the difference of three kernels:
--
--   • the centre-folded $\sigma$-twisted kernel $y\mapsto\sum^{\mathrm f}_{q\in\mathrm{GL}_2(L)/Z(\mathrm{GL}_2(L))}\int_{\mathbb A^\times}\xi_L(z)\,\varphi\bigl(x^{-1}\gamma_q\,\sigma_{\mathbb A}^{-1}(z\cdot y)\bigr)\,d\nu_Z(z)$, where $\gamma_q$ is the image in $G$ of a chosen representative of $q$, $z\cdot y$ means the product of the scalar matrix $z$ with $y$, and $\sum^{\mathrm f}$ is a finite-support sum;
--
--   • the cuspidal kernel $y\mapsto \mathrm{vol}\cdot\sum'_{\Psi}\ \sum^{\mathrm f}_{i:\,\mathrm{cls}(i)=\Psi}\ \bigl(A_\varphi b_i\bigr)(x)\,\overline{b_i(y)}$, the outer sum over the cuspidal classes for `pins`, $\xi_L$, $N$, $S_L$, where $\mathrm{vol}$ is the real number $\nu_Z\bigl(\Omega_L\cap\{z:\|\det(z\cdot 1)\|\in[\alpha,\beta]\}\bigr)$ viewed in $\mathbb C$ and $A_\varphi f=$ `twistedConvOp K L D σ φ f` is the twisted convolution $x\mapsto\int_G f(\sigma_{\mathbb A}(xh))\varphi(h)\,d\,$`adelicGLHaar`$(h)$;
--
--   • the residual kernel $y\mapsto \dfrac{\mathrm{vol}}{\mathrm{adelicGLHaar}(\Phi_0)}\sum^{\mathrm f}_{\chi}\bigl(A_\varphi(\chi\circ\det)\bigr)(x)\,(\chi^{-1}\circ\det)(y)$, the finite-support sum over those homomorphisms $\chi:\mathbb A^\times\to\mathbb C^\times$ with $\chi(z)^2=\xi_L(z)$ for all $z$ (`SquaresToXi`), trivial on the principal ideles and continuous.
--
--   The three statements are: for all sufficiently large $R$ the function $F_R$ is integrable on $\Phi_0$ for `adelicGLHaar`; the series $\sum_n \mathrm{cs}_n\,g(\mathrm{tabs}_n)$ is summable; and
--   $$\int_{\Phi_0}F_R\,d\,\mathrm{adelicGLHaar}\;-\;\Bigl(R\,\nu(g)+\sum_n \mathrm{cs}_n\,g(\mathrm{tabs}_n)+\mu(g)\Bigr)\longrightarrow 0$$
--   as $R\to+\infty$.
--
--   This is the continuous-spectrum (Eisenstein) block of the spectral side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$: the truncated centre-folded twisted kernel with its cuspidal and residual blocks subtracted, evaluated against the Hecke-word test functions and recorded as a linear growth term $R\,\nu(g)$, an absolutely convergent atomic part supported on Eisenstein eigensystem tables, and a remainder functional $\mu$ without point masses. It feeds the assembly of the full spectral side used in the base-change comparison along the Langlands–Tunnell route, being cited by [`AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_sub_lambdaT_tsum_finsum_twistedConvOp_sub_lambdaT_finsum_twistedConvOp_chiDet_sub.lean

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

theorem AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_sub_lambdaT_tsum_finsum_twistedConvOp_sub_lambdaT_finsum_twistedConvOp_chiDet_sub
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
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
    (hbc : ∀ ψ : AdelicGL2 (𝓞 L) L → ℂ,
      IsSmoothCuspAutomorphicFnAt L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL ψ →
      Continuous ψ →
      (∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).U N, ψ (g * k) = ψ g) →
      ψ ∈ archCutSubmodule L tysL →
      (∀ i, ∫ g in ΦL, ψ g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0) →
      ψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL] 0) :
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
        (∀ᶠ R : ℝ in Filter.atTop, IntegrableOn (fun x =>
            ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      AutomorphicForm.sigmaAdelicAct K L D σ.symm
                        (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
                x)))
            Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
        Summable (fun n : ℕ => cs n * g ⟨tabs n, htabs n⟩) ∧
        Filter.Tendsto (fun R : ℝ =>
          (∫ x in Φ₀,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      AutomorphicForm.sigmaAdelicAct K L D σ.symm
                        (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
                x))
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
          ((R : ℂ) * ν g + (∑' n, cs n * g ⟨tabs n, htabs n⟩) + μ g))
          Filter.atTop (nhds 0) := by sorry
