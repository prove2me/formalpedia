-- Prove2me | Theorems.Thm_AutomorphicForm_exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff
-- name    : AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/20d5410e-4515-526b-a3fb-89fa0f33f3f1
-- title:
--   One winding datum for all Hecke words (window side)
-- statement:
--   The setting is a cyclic extension of number fields. Fix number fields $K \subseteq L$ with $L/K$ Galois and finite, an automorphism $\sigma$ of $L$ over $K$ whose inverse generates the Galois group (hypothesis `hgen`: every $\tau$ lies in the cyclic group of integer powers of $\sigma^{-1}$), with $[L:K]$ prime (`hdeg`), and an idelic Galois descent datum $D$ for $\mathbb{A}_L$ over $K$ (a homomorphism from $\mathrm{Gal}(L/K)$ to continuous ring automorphisms of $\mathbb{A}_L$ compatible with the algebraic action on $L$).
--
--   The global truncation data consist of reals $0 < \alpha < \beta$; a set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ contained in the locus where the idele norm of the determinant lies in $[\alpha,\beta]$ (`hΦs`) and which is a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on that locus for the restricted adelic Haar measure (`hΦ`); a Haar measure $\nu_{Z_L}$ on $\mathbb{A}_L^{\times}$ with a fundamental domain $\Omega_L$ for the image of $L^{\times}$ (`hΩL`); and the corresponding $K$-side data $\Phi_K$, $\nu_{Z_K}$, $\Omega_K$ with the same two properties (`hΦKs`, `hΦK`, `hΩK`).
--
--   The ramification and level data consist of finite sets of finite places $S_K$ of $K$ and $S_L$ of $L$ with: every place of $L$ above $S_K$ lies in $S_L$ (`hSL`); membership in $S_L$ depends only on the place of $K$ below (`hSsat`); every place of $L$ whose trace lies outside $S_K$ is unramified, i.e. has ramification index $1$ (`hS`); an ideal $N$ of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`); an ideal $N'$ of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN'`); and archimedean type families $\mathrm{tys}_L$, $\mathrm{tys}_K$ (assignments, to each infinite place, of a finite list of finite-dimensional representations of the local row-isometry subgroup).
--
--   The central characters: $\xi_L$ is a homomorphism from the full unit group of $\mathbb{A}_L$ to $\mathbb{C}^{\times}$ that is continuous (`hξc`), trivial on the image of $L^{\times}$ (`hξt`), and takes the same value on the determinants of the Hecke generators $\mathrm{heckeGen}$ at any two places of $L$ outside $S_L$ lying over the same place of $K$ (`hξσ`). On the $K$-side, $\Xi$ is a finite set of homomorphisms characterised (`hΞ`) as exactly those $\xi$ that are continuous, trivial on the image of $K^{\times}$, and satisfy $\xi \circ (\text{idelic norm of the base change } K \to L) = \xi_L$.
--
--   The test-function and spectral-parameter data consist of functions $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, $\varphi_S$ on the semilocal groups $\mathrm{GL}_2(L \otimes_K K_v)$, $f_{a,K}$ on $\mathrm{GL}_2$ of the infinite adeles of $K$, and $f_{S,K}$ on the local groups $\mathrm{GL}_2(K_v)$; and a compact set $X$ of families of pairs of complex numbers indexed by the finite places of $L$ (`hXc`) which contains (`hX`) the set of those families $x$ vanishing at every $w \in S_L$ and satisfying, at every $w \notin S_L$, that $(x_w)_2$ equals the absolute norm of $w$ times $\xi_L(\det \mathrm{heckeGen}_w)$, that $\|(x_w)_1\| \le (\mathrm{absNorm}(w)+1)\sqrt{\|\xi_L(\det \mathrm{heckeGen}_w)\|}$, and the conjugation relation $\overline{(x_w)_1} = \overline{(x_w)_2}\,\|(x_w)_2\|^{-1}(x_w)_1$.
--
--   The hypothesis `hgeo` is the geometric-side comparison, assumed as an input: for every finite set $S' \supseteq S_K$, every continuous compactly supported $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ which is bi-invariant under the intersection of the level-one subgroup of $N$ with the finite-adelic subgroup, admits a semilocal factorisation above $S'$ with archimedean factor of the prescribed type and is archimedean bi-finite of type $\mathrm{tys}_L$, and every continuous compactly supported $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ unit-factorizable of type $\mathrm{tys}_K$ for the principal level of $N'$ intersected with the finite-adelic subgroup, such that $\varphi$ and $f$ are matching at $S'$ for $\sigma^{-1}$ and such that outside $S'$ the indicator functions of the semilocal and local integral sets are matching local functions: the twisted integral over $\Phi_L \times \Omega_L$ of $\xi_L(z)$ times the sum of $\varphi(x^{-1}\,\delta\,\sigma^{-1}(c(z)x))$ over the $\sigma$-conjugacy classes $\delta$ in $\mathrm{GL}_2(L)$ whose norm class is the conjugacy class of an elliptic or central element of $\mathrm{GL}_2(K)$, equals $c_0$ times the sum over $\xi_K \in \Xi$ of the integral over $\Phi_K \times \Omega_K$ of $\xi_K(z)$ times the sum of the central and elliptic parts of the adelic kernel of $f$ at $(x, c(z)x)$.
--
--   The Hecke data at the auxiliary set $T$: $T$ is a finite set of finite places of $K$ disjoint from $S_K$ (`hTdisj`) with at least two elements (`hT2`), such that no place of $L$ above a place of $T$ lies in $S_L$ (`hTSL`); $\mathrm{ws}$ chooses, for each $v$, an extension of $v$ to $L$; $w'$ is a further assignment of places of $L$ with $(w'v)$ the ideal $\sigma^{-1}$-translate of $\mathrm{ws}(v)$ for $v \in T$ (`hw'`); $\varpi_s$, $\varpi_{K,s}$ are chosen integral elements which at places of $T$ are irreducible and have nonzero image in the completion (`hϖirr`, `hϖs0`, `hϖKirr`, `hϖKs0`); $r_{T,s}$ and $r_{K,s}$ are finite families of representatives forming Hecke coset systems for the integral subgroup and the diagonal element $\mathrm{diagPi}$ at the semilocal and local places of $T$ (`hrTs`, `hrKs`); and $z_s$, $z_{K,s}$ are the scalar matrices with entry $\varpi_s$, resp. $\varpi_{K,s}$, at places of $T$ (`hzs`, `hzKs`).
--
--   The unramifiedness hypothesis `hur` states that every $\xi \in \Xi$ is trivial on the local units of valuation $1$ at every place outside $S_K$, embedded into the ideles. The norm compatibilities are: at $v \in T$, the absolute norms of $\mathrm{ws}(v)$ and of $w'(v)$ agree (`hNw'`), and this common norm is the absolute norm of $v$ raised to the slot degree $\mathrm{slotDeg}$, the inertia degree of $\mathrm{ws}(v)$ over $v$ (`hNwf'`); $s$ is a family of complex numbers with $s(v)^2 = \xi_L(\det \mathrm{heckeGen}_{w'(v)})$ for $v \in T$ (`hs`); and for every $\xi \in \Xi$ and $v \in T$ the $\mathrm{slotDeg}$-th power of $\xi(\det\mathrm{heckeGen}_v)$ equals $\xi_L(\det\mathrm{heckeGen}_{w'(v)})$ (`hxK`).
--
--   The local harmonic-analysis data on the $K$-side: $f_{a,K}$ is an archimedean test factor (smooth with compact support, given by a smooth function of the matrix entries in the mixed space) (`hfaK`); $f_{S,K}(v)$ is a locally constant compactly supported function for $v \in S_K$ (`hfSK`); reals $\kappa_{0K}$, $\kappa_K$, $c_{\tau K} > 0$; a measure $\nu_A$ on the archimedean group and a constant $c_G$ for which the factorisation hypothesis `hG` holds: for every finite $S$ and every triple $(f, f_a, f_S)$ with the stated measurability, which factorises as the archimedean factor times the product of the local factors on elements integral outside $S$ and vanishes when some component outside $S$ is non-integral, the adelic Haar integral of $f$ equals $c_G$ times the archimedean integral times the product of the local integrals. Similarly, for each $u \in K^{\times}$ and $z \in \mathbb{A}_K^{\times}$, measures $\tau_G(u,z)$ on the centraliser of $c(z)\,\mathrm{diag}(u,1)$ in $\mathrm{GL}_2(\mathbb{A}_K)$, $\tau_A(u,z)$ on the archimedean centraliser and $\tau_F(u,z,v)$ on the local centralisers, all Haar for $u \ne 1$ (`hτG`, `hτA`, `hτF`), with $\tau_G$ computing as $c_{\tau K}$ times the integral over the diagonal torus $\mathbb{A}_K^{\times} \times \mathbb{A}_K^{\times}$ (`hτGc`), $\tau_F$ of mass $1$ on the preimage of the local integral set (`hτF1`), and a constant $c_T > 0$ with the analogous centraliser factorisation hypothesis `hT`. Orbital integrals: $I_A(u,z)$ is an orbital integral of $f_{a,K}$ at the archimedean component of $c(z)\mathrm{diag}(u,1)$ for $\tau_A$ (`hIA`), and $I_F(u,z,v)$ the local orbital integral of $f_{S,K}(v)$ at $v \in S_K$ (`hIF`); $J_A$ and $J_F$ are the corresponding weighted orbital integrals, with archimedean weight $-\log$ of the archimedean height minus $-\log$ of the archimedean height after translation by the adelic Weyl element (`hJA`), and with the local weight $\mathrm{LocalWeight.weight}$ at $v \in S_K$ (`hJF`).
--
--   The matching hypotheses: $\varphi_a$ is an archimedean test factor (`hφa`); $\varphi_S(v)$ is a locally constant compactly supported function on the semilocal group for $v \in S_K$ (`hφS`); $\varphi_a$ matches $f_{a,K}$ archimedeanly (`hmatchA`) and $\varphi_S(v)$ matches $f_{S,K}(v)$ locally for $v \in S_K$ (`hmatchS`), both for $\sigma^{-1}$.
--
--   The twisted side: reals $\kappa_{0L}$, $\kappa_L$, $c_G' > 0$, $c_T' > 0$, $C > 0$; a measure $\nu_A'$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$, with $\nu_A$ pinned to the archimedean Haar measure on the $K$-side and $\nu_A'$ to that on the $L$-side (`hνA`, `hνA'`); lifts $\delta_A(u,z)$ whose norm string equals the image of the archimedean component of $c(z)\mathrm{diag}(u,1)$ in the tensor group whenever that component is a norm (`hδA`), with Haar measures $\tau_A'(u,z)$ on the associated twisted centralisers (`hτA'`) coupled to $\tau_A(u,z)$ through the conjugator $1$ (`hτA'c`); lifts $\delta_F(u,z,v)$ with the analogous property at $v \in S_K$ (`hδF`) and Haar measures $\tau_F'(u,z,v)$ of mass $1$ on the preimage of the semilocal integral set (`hτF'`, `hτF'1`); twisted weighted orbital integrals $J_A'(u,z)$ of $\varphi_a \circ \mathrm{archIdentGL}$ for the archimedean weight built from the $L$-side archimedean heights (`hJA'`), vanishing when the relevant class is not a norm (`hJA'0`), and $J_F'(u,z,v)$ of $\varphi_S(v)$ at $v \in S_K$ (`hJF'`), likewise vanishing in the non-norm case (`hJF'0`). Finally a free complex scalar $\kappa_m$.
--
--   The conclusion asserts the existence of a single winding datum $\mathcal{B}$ of signature $(r,d,c) = (\#\{\text{infinite places of } K\},\ |T|,\ \#\{\text{infinite places of } K\} + |T|)$ — a structure comprising a discrete lattice $\Lambda$ in $(\mathbb{R}^r) \times (\mathbb{Z}^d)$, a linear functional and a frequency vector satisfying the pairing identity on $\Lambda$, a character of $\Lambda$, a sequence of subgroups of $\Lambda$, and a sequence of continuous integrable test functions with quadratic decay bounds on themselves and their Fourier transforms, together with the remaining combinatorial data — such that the following holds for every choice of exponent families $ks$, $js$ of natural numbers indexed by the finite places of $K$, every finite set $\Delta_K$ of elements of $\mathrm{GL}_2(K)$ that are diagonal with ratio of diagonal entries $\ne 1$ (`hΔK`) and are distinguished by that ratio (`hΔKinj`), every family $I_W$ of orbital integrals at $v \in T$ of the Hecke-word test function $x \mapsto \sum_{\iota} \mathbf{1}_{\text{integral}}\big(((\prod_m r_{K,s}(v)(\iota(m)))\, z_{K,s}(v)^{m(v)_1})^{-1} x\big)$, the sum running over maps $\iota$ from $\mathrm{Fin}(m(v)_0)$ to the coset index set, for each multi-index $m$ in the slot index set $\mathrm{slotIndex}$ (the set of $T$-indexed families of exponent pairs in the supports of the slot words) (`hIW`), every family $I_U$ of orbital integrals of the indicator of the local integral set at $v \notin S_K \cup T$ (`hIU`), every pair of maps $u_K$, $d_K$ recording for $\gamma \in \Delta_K$ the ratio of diagonal entries and the lower diagonal entry (`huK`, `hdK`), and every family $W_K$ satisfying (`hWK`) for $m$ in the slot index set, $\gamma \in \Delta_K$ and $z$: $W_K(m,\gamma,z)$ is the product of $\prod_{v\in T} I_W(m)(u_K\gamma, z\,d_K\gamma, v)$, the finitary product $\prod_{v \notin S_K \cup T} I_U(u_K\gamma, z\,d_K\gamma, v)$, and the bracket
--   $$\big(J_A' - [L:K]\,J_A\big)\prod_{v \in S_K} I_F \; + \; I_A \sum_{v \in S_K}\big(J_F'(v) - [L:K]\,J_F(v)\big)\prod_{v' \in S_K \setminus \{v\}} I_F(v'),$$
--   all arguments being $(u_K\gamma, z\,d_K\gamma)$; and subject to the completeness hypothesis `hΔKc` that for $m$ in the slot index set and any $u \ne 1$ whose ratio is attained by no $\gamma \in \Delta_K$, the same bracket expression with $u$ in place of $u_K\gamma$ vanishes for all $z$ — then
--   $$\kappa_m \cdot \frac{c_G' c_T'^{-1}\,\kappa_{0L}\,\kappa_L\,C}{|\Xi|}\sum_{m \in \mathrm{slotIndex}} \mathrm{slotFamilyCoeff}(m) \sum_{\gamma \in \Delta_K}\sum_{\xi \in \Xi} \int_{\mathbb{A}_K^{\times}} \xi(z)\, W_K(m,\gamma,z)\, d\nu_{Z_K}$$
--   equals
--   $$\sum_{n} \Big(\prod_{i : \mathrm{Fin}(|T|)} \big(\sqrt{\mathrm{absNorm}\,w'(v_i)}\; s(v_i)\big)^{k_{v_i}}\; \xi_L\big(\det \mathrm{heckeGen}_{w'(v_i)}\big)^{j_{v_i}}\; \big[(T_1+T_{-1})^{k_{v_i}}\big]_{n_i}\Big)\,\mathcal{B}.\mathrm{coeff}(n),$$
--   where $v_i$ denotes the $i$-th place of $T$ under the chosen enumeration, the outer sum runs over the integer box $\prod_i [-k_{v_i}, k_{v_i}]$, $[\,\cdot\,]_{n_i}$ denotes the coefficient of $T^{n_i}$ in the indicated power of $T + T^{-1}$ in the ring of Laurent polynomials over $\mathbb{C}$, and $\mathrm{slotFamilyCoeff}$ is the product over $v \in T$ of the slot coefficients attached to $(k_v, j_v)$ and $m_v$.
--
--   Thus one winding datum serves all Hecke words $(ks, js)$ simultaneously, the word-dependence being carried entirely by the explicit Satake–Laurent factors on the right.
--
--   This is the window-side packaging step in the comparison of hyperbolic (diagonal) terms between the twisted trace formula for a cyclic prime-degree extension $L/K$ and the trace formula for $K$: the class sums of the unweighted window brackets over diagonal representatives, summed against the central characters in $\Xi$ and weighted by the Satake slot coefficients, are realised as the pairing of an explicit Laurent-coefficient box with the coefficients of a single winding datum, uniformly in the Hecke word. It is used by the assembly of the hyperbolic-intercept identity, where the difference between the twisted and $[L:K]$-fold untwisted weighted orbital contributions is identified with an affine expression in the Hecke word.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff.lean

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
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel
open LanglandsTunnell.CubicInduction (diagUnits2)

open AutomorphicForm in
open scoped TensorProduct.RightActions in
open scoped Classical in

theorem AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff
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

    (T : Finset (HeightOneSpectrum (𝓞 K))) (hTdisj : Disjoint T SK) (hT2 : 2 ≤ T.card)
    (hTSL : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (hw' : ∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal)
    (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
    (hϖirr : ∀ v ∈ T, Irreducible (ϖs v))
    (hϖs0 : ∀ v ∈ T, algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrTs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))
    (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hϖKirr : ∀ v ∈ T, Irreducible (ϖKs v))
    (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (hrKs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))

    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (hNw' : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm (w' v).asIdeal)
    (hNwf' : ∀ v ∈ T, Ideal.absNorm (w' v).asIdeal =
      Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (s : HeightOneSpectrum (𝓞 K) → ℂ)
    (hs : ∀ v ∈ T, s v ^ 2 =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hxK : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          AutomorphicForm.SatakeCombination.slotDeg K L ws v =
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (κ₀K κK : ℝ) (cτK : ℝ) (hcτK : 0 < cτK)
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa νA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))

    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))

    (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (hφS : ∀ v ∈ SK, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))
    (hmatchA : AutomorphicForm.AreMatchingArch K L σ.symm φa faK)
    (hmatchS : ∀ v ∈ SK, AutomorphicForm.AreMatchingLocal K L v σ.symm (φS v) (fSK v))

    (κ₀L κL cG' cT' C : ℝ) (hcG' : 0 < cG') (hcT' : 0 < cT') (hC : 0 < C)

    (JA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (JA u z))
    (JF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsWeightedOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (JF u z v))

    (νA' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hνA : νA = AutomorphicForm.archHaarK K) (hνA' : νA' = AutomorphicForm.archHaarL K L)
    (δA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ.symm (δA u z) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ.symm (δA u z)))
    (hτA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τA' u z).IsHaarMeasure)
    (hτA'c : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ.symm (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (δA u z) 1 (τA u z) (τA' u z))
    (δF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.normString K L (v.adicCompletion K) σ.symm (δF u z v) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ.symm (δF u z v)))
    (hτF' : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → (τF' u z v).IsHaarMeasure)
    (hτF'1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (JA' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ.symm νA'
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
        (δA u z) (τA' u z) (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u z))
    (hJA'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ.symm (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) → JA' u z = 0)
    (JF' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ.symm (δF u z v) (τF' u z v) (φS v) (JF' u z v))
    (hJF'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ.symm (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      JF' u z v = 0)

    (κm : ℂ) :
    ∃ ℬ : AutomorphicForm.WindingDatum (Fintype.card (NumberField.InfinitePlace K)) T.card
        (Fintype.card (NumberField.InfinitePlace K) + T.card),
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
      (ΔK : Finset (GL (Fin 2) K))
      (hΔK : ∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
      (hΔKinj : ∀ γ ∈ ΔK, ∀ γ' ∈ ΔK,
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 =
          (γ' : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ' : Matrix (Fin 2) (Fin 2) K) 1 1 → γ = γ')
      (IW : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
      (hIW : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ u z, ((u : Kˣ) : K) ≠ 1 →
        ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T), AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v)
            (fun x : GL (Fin 2) (v.adicCompletion K) =>
              ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)) (IW m u z v))
      (IU : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
      (hIU : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∉ SK ∪ T, AutomorphicForm.IsOrbitalIntegral K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v)
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (IU u z v))

      (uK dK : GL (Fin 2) K → Kˣ)
      (huK : ∀ γ ∈ ΔK, (uK γ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1)
      (hdK : ∀ γ ∈ ΔK, (dK γ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 1 1)

      (WK : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
      (hWK : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ γ ∈ ΔK, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        WK m γ z =
          (∏ v ∈ T, IW m (uK γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dK γ))) v) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU (uK γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dK γ))) v) *
          ((JA' (uK γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dK γ))) - (Module.finrank K L : ℂ) * JA (uK γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dK γ)))) * ∏ v ∈ SK, IF (uK γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dK γ))) v +
              IA (uK γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dK γ))) * ∑ v ∈ SK, (JF' (uK γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dK γ))) v - (Module.finrank K L : ℂ) * JF (uK γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dK γ))) v) * ∏ v' ∈ SK.erase v, IF (uK γ) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (dK γ))) v'))

      (hΔKc : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ u : Kˣ, (u : K) ≠ 1 →
        (∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ (u : K)) →
          ∀ z : (AdeleRing (𝓞 K) K)ˣ,
            (∏ v ∈ T, IW m u z v) *
            (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ SK ∪ T), IU u z v) *
            ((JA' u z - (Module.finrank K L : ℂ) * JA u z) * ∏ v ∈ SK, IF u z v +
              IA u z * ∑ v ∈ SK, (JF' u z v - (Module.finrank K L : ℂ) * JF u z v) * ∏ v' ∈ SK.erase v, IF u z v') = 0)
      , κm * ((((cG' * cT'⁻¹ : ℝ) : ℂ) * (κ₀L : ℂ) * ((κL : ℝ) : ℂ) * ((C : ℝ) : ℂ) / (Ξ.card : ℂ)) *
      ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∑ γ ∈ ΔK,
              ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WK m γ z ∂νZK) =
        ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * ℬ.coeff n := by sorry
