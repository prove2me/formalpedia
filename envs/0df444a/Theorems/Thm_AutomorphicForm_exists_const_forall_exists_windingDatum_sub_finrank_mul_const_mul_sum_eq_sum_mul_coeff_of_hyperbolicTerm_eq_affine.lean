-- Prove2me | Theorems.Thm_AutomorphicForm_exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine
-- name    : AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/0bb8e8dc-6567-5707-a177-19324d865ed1
-- title:
--   A uniform transfer constant in the twisted hyperbolic comparison
-- statement:
--   **Setting.** $K$ and $L$ are number fields with $L/K$ a finite Galois extension of prime degree $[L:K]=\operatorname{finrank}_K L$ (hypothesis `hdeg`), $\sigma : L \simeq_K L$ is an automorphism such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the group of integer powers of $\sigma^{-1}$ (`hgen`), and $D$ is an `IdeleGaloisDescent` datum for $\mathcal{O}_L$ over $K$, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$, continuous and compatible with the action on $L$; `sigmaAdelicAct` denotes the induced action on $\mathrm{GL}_2(\mathbb{A}_L)$, and `globalPoints` the embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_F)$, `centralScalar` the embedding of ideles as central scalar matrices.
--
--   **Windows and fundamental domains.** Real numbers $\alpha, \beta$ satisfy $0 < \alpha < \beta$. On the $L$ side, $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ is contained in the norm slab $\{g : \lVert \det g \rVert_L \in [\alpha,\beta]\}$ (`hΦs`, with `ideleNorm` the Haar-character norm) and is a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to adelic Haar measure restricted to that slab (`hΦ`); $\nu_{Z,L}$ is a Haar measure on $\mathbb{A}_L^\times$ and $\Omega_L$ a fundamental domain for the principal ideles of $L$ in $\mathbb{A}_L^\times$ (`hΩL`). The data $\Phi_K$ (`hΦKs`, `hΦK`), $\nu_{Z,K}$, $\Omega_K$ (`hΩK`) are the exact analogues over $K$.
--
--   **Place sets.** $S_K$ and $S_L$ are finite sets of finite places of $K$ and of $L$: every place of $L$ over a place of $S_K$ lies in $S_L$ (`hSL`); membership in $S_L$ depends only on the place of $K$ below (`hSsat`); and every place $w$ of $L$ whose place below is outside $S_K$ is unramified, $e(w) = 1$ (`hS`).
--
--   **Central characters.** $\xi_L$ is a homomorphism from the full subgroup $\top \le \mathbb{A}_L^\times$ to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the principal ideles (`hξt`), and taking the same value on $\det$ of the adelic Hecke generators `heckeGen` at any two places outside $S_L$ lying over the same place of $K$ (`hξσ`). On the $K$ side, $\Xi$ is a finite set of homomorphisms $\top \le \mathbb{A}_K^\times \to \mathbb{C}^\times$ which, by `hΞ`, consists exactly of those characters that are continuous, trivial on the principal ideles of $K$, and whose composite with the idelic norm of the base change `genuineBaseChange K L` equals $\xi_L$.
--
--   **Levels, archimedean types, test data.** $N$ is an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`) and $N'$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN'`); $\mathrm{tys}_L$, $\mathrm{tys}_K$ are archimedean type families (a number of representations chosen at each infinite place). Further, $\varphi_a$ is a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, $\varphi_S$ assigns to each finite place $v$ of $K$ a function on $\mathrm{GL}_2(L \otimes_K K_v)$, and $f_{a,K}$, $f_{S,K}$ are the corresponding archimedean and local data over $K$. Finally $X$ is a compact set (`hXc`) of functions assigning to each finite place of $L$ a pair of complex numbers, which contains (`hX`) every $x$ that vanishes at all $w \in S_L$ and satisfies, for $w \notin S_L$: $(x\,w)_2 = \mathrm{N}(w)\,\xi_L(\det \mathrm{heckeGen}(w))$, $\lVert (x\,w)_1 \rVert \le (\mathrm{N}(w)+1)\sqrt{\lVert \xi_L(\det \mathrm{heckeGen}(w))\rVert}$, and $\overline{(x\,w)_1} = \overline{(x\,w)_2}\,\lVert (x\,w)_2 \rVert^{-1} (x\,w)_1$.
--
--   **The input comparison.** A complex number $c_0$ is given together with the hypothesis `hgeo`: for every finite $S' \supseteq S_K$ and every pair $(\varphi, f)$ of continuous compactly supported functions on $\mathrm{GL}_2(\mathbb{A}_L)$, $\mathrm{GL}_2(\mathbb{A}_K)$ such that $\varphi$ is unit factorizable above $S'$ of archimedean type $\mathrm{tys}_L$ for the level $\mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, $f$ is unit factorizable at $S'$ of archimedean type $\mathrm{tys}_K$ for $\mathrm{principalLevel}(N') \sqcap \ker(\mathrm{glArch})$, $\varphi$ and $f$ are matching at $S'$ relative to $\sigma^{-1}$, and at every $v \notin S'$ all of whose extensions to $L$ are unramified the indicator functions of the semi-local and local integral sets are locally matching, one has
--   $$\int_{\Phi_L}\int_{\Omega_L} \xi_L(z) \sum_{\delta} \varphi\bigl(x^{-1}\,\delta\,{}^{\sigma^{-1}}(z\,x)\bigr) = c_0 \sum_{\xi_K \in \Xi} \int_{\Phi_K}\int_{\Omega_K} \xi_K(z)\bigl(\mathrm{adelicKernelCentralPart}(f) + \mathrm{adelicKernelEllipticPart}(f)\bigr)(x, z\,x),$$
--   where $\delta$ runs over those elements of $\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted conjugacy class has norm class equal to the conjugacy class of some $\gamma \in \mathrm{GL}_2(K)$ lying in the elliptic or the central cell, and the two kernel parts are the sums of $f(x^{-1}\gamma y)$ over the central, respectively elliptic, cells.
--
--   **Conclusion.** There exists $\lambda \in \mathbb{C}$ with $\lambda \ne 0$ such that the following two assertions hold.
--
--   (i) If there exist a finite $S' \supseteq S_K$ and functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, both continuous with compact support, with $\varphi$ unit factorizable above $S'$ of type $\mathrm{tys}_L$ for $\mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, $f$ unit factorizable at $S'$ of type $\mathrm{tys}_K$ for $\mathrm{principalLevel}(N') \sqcap \ker(\mathrm{glArch})$, matching at $S'$ relative to $\sigma^{-1}$ and with the unramified local matching of indicator functions at every $v \notin S'$ as above, for which the $K$-side fold $\sum_{\xi_K \in \Xi} \int_{\Phi_K}\int_{\Omega_K} \xi_K(z)(\mathrm{adelicKernelCentralPart}(f) + \mathrm{adelicKernelEllipticPart}(f))(x, z\,x)$ is non-zero, then $[L:K]\,\lambda = c_0$.
--
--   (ii) For every finite set $T$ of finite places of $K$ disjoint from $S_K$ with $2 \le \lvert T \rvert$ and such that no place of $L$ above a place of $T$ lies in $S_L$; for every choice of an extension $w_v$ of each place $v$ to $L$ and of a map $w'$ with $(w'(v)) = \sigma^{-1}\cdot(w_v)$ as ideals for $v \in T$; for every family of uniformisers $\varpi_v$ in the valuation ring of $L_{w_v}$, irreducible and with non-zero image in $L_{w_v}$ for $v \in T$; for every family $r_{T,v} : \mathrm{Fin}(n_v) \to \mathrm{GL}_2(L_{w_v})$ which, for $v \in T$, is a Hecke coset system for the integral subgroup of $\mathrm{GL}_2(L_{w_v})$ and the element $\mathrm{diag}(\varpi_v, 1)$ (each representative lies in the double coset, the representatives cover it modulo the integral subgroup, and their classes are distinct); for every family $z_v \in \mathrm{GL}_2(L_{w_v})$ equal to $\varpi_v$ times the identity matrix for $v \in T$; and for the analogous data $\varpi_{K,v}$, $n_{K,v}$, $r_{K,v}$, $z_{K,v}$ over the completions $K_v$ — there exist natural numbers $r$, $c$, a function $s$ from the finite places of $K$ to $\mathbb{C}$, and two winding data $\mathcal{A}, \mathcal{B}$ of shape $(r, \lvert T \rvert, c)$ (each a `WindingDatum`: a discrete lattice in $(\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,\lvert T\rvert \to \mathbb{Z})$, a linear functional and a non-zero frequency vector compatible on the lattice, a character into $c$ copies of $\mathbb{R}/\mathbb{Z}$, a sequence of subgroups, and sequences of continuous integrable profile functions with quadratic decay bounds on them and on their Fourier transforms, together with integer and phase parameters; its coefficient function $\mathcal{D}.\mathrm{coeff}$ is the resulting absolutely convergent series indexed by $\mathrm{Fin}\,\lvert T\rvert \to \mathbb{Z}$) such that:
--
--   $s(v)^2 = \xi_L(\det \mathrm{heckeGen}(w'(v)))$ for all $v \in T$; and for all exponent functions $k$, $j$ on the finite places of $K$, every continuous compactly supported $\varphi_L$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that $\varphi_L$ is a semi-local factorisation over $S_K \cup T$ with archimedean factor $\varphi_a$, finite factor $\varphi_f$ and semi-local factors given at $v \in T$ by the Hecke word sum $x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf{1}_{\text{semi-local integral set}}\bigl(\text{(semi-local component of the local embedding of } \prod_m r_{T,v}(\iota\,m) \cdot z_v^{\,j_v})^{-1} x\bigr)$ and at $v \notin T$ by $\varphi_S(v)$ (`hSLF`), with $\varphi_L$ bi-invariant under $\mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$ (`hbi`) and archimedeanly bi-finite of type $\mathrm{tys}_L$ (`harch`); and every family $\mathrm{fam}$ of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ indexed by slot multi-indices $m$ such that (`hfam`) for every $m$ in the slot index set $\mathrm{slotIndex}(w, k, j, T)$ the function $\mathrm{fam}(m)$ is bi-invariant under $\mathrm{principalLevel}(N') \sqcap \ker(\mathrm{glArch})$, archimedeanly bi-finite of type $\mathrm{tys}_K$, $f_{a,K}$ is an archimedean test factor and each $f_{S,K}(v)$, $v \in S_K$, a local test function, and there is a finite test factor $f\!f$ which on elements with integral components outside $S_K \cup T$ equals the product over $v \in S_K \cup T$ of the local Hecke word sum with exponents $m(v)(0)$, $m(v)(1)$ for $v \in T$ and of $f_{S,K}(v)$ otherwise, vanishes when some component outside $S_K \cup T$ is non-integral, and satisfies $\mathrm{fam}(m)(g) = f_{a,K}(g_\infty)\,f\!f(g_{\mathrm{fin}})$; and such that $\varphi_L$ matches $\sum_m \mathrm{slotFamilyCoeff}(m)\,\mathrm{fam}(m)$ at $S_K \cup T$ relative to $\sigma^{-1}$ (`hmatch`) — the following holds.
--
--   For all complex numbers $A_L$, $B_L$, all functions $A_K, B_K$ assigning to a character of $\top \le \mathbb{A}_K^\times$ and a slot multi-index a complex number, and all $R_0 \in \mathbb{R}$: if for every $R \ge R_0$ the $\xi_L$-twisted integral over the canonical truncation domain of $L$ (for $\alpha, \beta$) and over $\Omega_L$ of the twisted hyperbolic fold — the sum of $\varphi_L(x^{-1}\delta\,{}^{\sigma^{-1}}(z\,x))$ over the $\delta$ whose twisted norm class is the class of a hyperbolic $\gamma \in \mathrm{GL}_2(K)$ — minus the indicator of the set where the adelic height of $L$ exceeds $e^R$ times the constant term, formed along the unipotent family $t \mapsto \begin{pmatrix}1&t\\0&1\end{pmatrix}$ with the measure of the production pin data for $L$ (adelic additive Haar conditioned on the adelic box), of the degenerate sum over $\{\delta : \delta_{10} = 0,\ \mathrm{N}_{L/K}(\delta_{00}/\delta_{11}) \ne 1\}$, equals $R\,A_L + B_L$, and likewise for every $\xi_K \in \Xi$ and every slot index $m$ the corresponding $K$-side truncated integral of $\mathrm{adelicKernelHyperbolicPart}(\mathrm{fam}(m))$ minus the analogous high-height constant term (over $\{\gamma : \gamma_{10} = 0,\ \gamma_{00}/\gamma_{11} \ne 1\}$) equals $R\,A_K(\xi_K)(m) + B_K(\xi_K)(m)$, then
--   $$A_L - [L:K]\,\lambda \sum_{\xi_K \in \Xi} \sum_{m} \mathrm{slotFamilyCoeff}(m)\,A_K(\xi_K)(m) = \sum_{n} \Bigl(\prod_{i} \bigl(\sqrt{\mathrm{N}(w'(v_i))}\,s(v_i)\bigr)^{k_{v_i}} \xi_L\bigl(\det \mathrm{heckeGen}(w'(v_i))\bigr)^{j_{v_i}} \bigl[(T + T^{-1})^{k_{v_i}}\bigr]_{n_i}\Bigr)\,\mathcal{A}.\mathrm{coeff}(n),$$
--   and the same identity with $A_L$, $A_K$, $\mathcal{A}$ replaced by $B_L$, $B_K$, $\mathcal{B}$. Here $i$ runs over $\mathrm{Fin}\,\lvert T\rvert$ with $v_i$ the corresponding place of $T$ under the chosen enumeration, $n$ runs over the product of the integer intervals $[-k_{v_i}, k_{v_i}]$, and $[(T+T^{-1})^{k}]_{n_i}$ denotes the coefficient at $n_i$ of the indicated Laurent polynomial over $\mathbb{C}$.
--
--   This is the winding (hyperbolic-term) half of the comparison of twisted and untwisted trace formulae for $\mathrm{GL}_2$ in base change for a prime-degree cyclic extension: the central and elliptic comparison supplies a constant $c_0$, and the statement produces a single non-zero transfer constant $\lambda$, independent of the auxiliary set $T$ of Hecke places and of all word and coset data, such that the slope and intercept of the truncated hyperbolic contributions differ, after the factor $[L:K]\lambda$, by sums of winding-datum coefficients weighted by Satake–Laurent coefficients. It feeds the downstream assembly [`AutomorphicForm.exists_const_forall_exists_windingDatum_integrableOn_and_hyperbolicTerm_sub_finrank_mul_const_mul_sum_eq_mul_sum_coeff_add_sum_coeff_of_areMatchingAt`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_integrableOn_and_hyperbolicTerm_sub_finrank_mul_const_mul_sum_eq_mul_sum_coeff_add_sum_coeff_of_areMatchingAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine
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
      ((∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧
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
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) →
        (Module.finrank K L : ℂ) * lam = c₀) ∧
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
      ∃ (r c : ℕ) (s : HeightOneSpectrum (𝓞 K) → ℂ)
        (𝒜 ℬ : AutomorphicForm.WindingDatum r T.card c),
      (∀ v ∈ T, s v ^ 2 = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ) (hφL : Continuous φL) (hφLc : HasCompactSupport φL)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
        (hSLF : IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))
        (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φL)
        (harch : IsArchBiFinite L tysL φL)
        (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ)
        (hfam : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
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
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
        (hmatch : AreMatchingAt K L σ.symm (SK ∪ T) φL
          (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x)),
      ∀ (AL BL : ℂ) (AK BK : (((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → ℂ))) (R₀ : ℝ),
        (∀ R : ℝ, R₀ ≤ R →
          (∫ x in AutomorphicForm.canonicalTruncationDomain L α β, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = (R : ℂ) * AL + BL ∧
          ∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (R : ℂ) * AK ξK m + BK ξK m) →
      (AL - (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * AK ξK m =
          ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * 𝒜.coeff n) ∧
      (BL - (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * BK ξK m =
          ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * ℬ.coeff n) := by sorry
