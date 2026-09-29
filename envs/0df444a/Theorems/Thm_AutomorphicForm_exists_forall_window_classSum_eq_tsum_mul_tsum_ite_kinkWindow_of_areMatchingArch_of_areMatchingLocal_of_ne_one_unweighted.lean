-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted
-- name    : AutomorphicForm.exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/1b4df63c-8cec-5974-960e-aad1e22aafbc
-- title:
--   Intercept class sums as lattice sums of kink windows
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ an algebra over $K$, $r$ denotes the number of infinite places of $K$ and $m = |T|$ for the finite set of primes $T$ introduced below; $\gamma(u,z)$ denotes the element $z \cdot \mathrm{diag}(u,1)$ of $GL_2(\mathbb{A}_K)$, i.e. the product of the central scalar matrix attached to an idele unit $z$ and of `diagUnits2` applied to the principal idele of $u \in K^\times$ and to $1$; $\gamma_\infty(u,z)$ and $\gamma_v(u,z)$ denote its archimedean component (`glArch`) and the $v$-component of its finite part (`finComponent` of `glFin`).
--
--   **Place and character data.** A family `ws` assigning to each finite place $v$ of $K$ a height-one prime of $\mathcal{O}_L$ lying under $v$; a Haar measure $\nu_{ZK}$ on the idele units $(\mathbb{A}_K)^\times$ (with its Borel structure); a finite set $\Xi$ of homomorphisms from the full subgroup of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, each continuous as a $\mathbb{C}$-valued function on $(\mathbb{A}_K)^\times$ (`hΞc`), each trivial on the image of $K^\times$ (`hΞt`), and each unramified outside $S_K$ in the sense that $\xi$ takes the value $1$ on the idele which is a local unit $t$ of valuation $1$ at $v \notin S_K$ and $1$ elsewhere (`hur`); two disjoint finite sets $S_K, T$ of finite places of $K$ with $|T| \ge 2$.
--
--   **Norm and Satake data.** A function $Nw$ with, for $v \in T$, $Nw(v)$ the absolute norm of the ideal of the chosen prime `ws v` (`hNw`) and also $Nw(v) = (\mathrm{absNorm}\,v)^{f_v}$, where $f_v =$ `SatakeCombination.slotDeg K L ws v` is the inertia degree of `ws v` over $v$ (`hNwf`); complex-valued functions $\zeta, s$ on finite places with $\zeta_v \ne 0$ for $v \in T$ (`hζ`), $s_v^2 = \zeta_v$ for $v \in T$ (`hs`), and $\xi(\det \mathrm{heckeGen}_v)^{f_v} = \zeta_v$ for all $\xi \in \Xi$, $v \in T$ (`hx`).
--
--   **Test data on the $K$-side.** A function $f_{aK}$ on $GL_2(\mathbb{A}_{K,\infty})$ which is an archimedean test factor, i.e. of compact support and of the form $g \mapsto \Phi(\mathrm{archEntries}\,g)$ for a smooth $\Phi$ on matrices over the mixed space of $K$ (`hfaK`); functions $f_{S_K,v}$ on $GL_2(K_v)$ which, for $v \in S_K$, are locally constant of compact support (`hfSK`); real constants $\kappa_{0K}, \kappa_K$; a measure $\nu_A$ on $GL_2(\mathbb{A}_{K,\infty})$ for the Borel structure `glBorelOf`.
--
--   **Tori and their measures.** A constant $c_{\tau K} > 0$; measures $\tau_G(u,z)$ on the centraliser of $\gamma(u,z)$ in $GL_2(\mathbb{A}_K)$ which, for $u \ne 1$, are Haar (`hτG`) and satisfy $\int g \, d\tau_G(u,z) = c_{\tau K} \int g(\mathrm{diag}(p_1,p_2)) \, d(\nu_{ZK} \times \nu_{ZK})$ for every $g$ (`hτGc`); measures $\tau_A(u,z)$ on the centraliser of $\gamma_\infty(u,z)$, Haar for $u \ne 1$ (`hτA`); measures $\tau_F(u,z,v)$ on the local centraliser of $\gamma_v(u,z)$, Haar for $u \ne 1$ (`hτF`) and of total mass $1$ on the preimage of the local integral set $\{g : g, g^{-1} \text{ have entries in } \mathcal{O}_{K_v}\}$ (`hτF1`). A constant $c_T > 0$ and the factorisation hypothesis `hT`: for all $u \ne 1$, $z$, every finite set $S$ of finite places and all functions $W$ on $GL_2(\mathbb{A}_K)$, $W_a$ on $GL_2(\mathbb{A}_{K,\infty})$ and $W_{S,v}$ on $GL_2(K_v)$ such that $W_a$ is a.e. strongly measurable for $\tau_A(u,z)$, each $W_{S,v}$ ($v \in S$) is a.e. strongly measurable for $\tau_F(u,z,v)$, $W(t) = W_a(t_\infty)\prod_{v \in S} W_{S,v}(t_v)$ for every $t$ in the centraliser all of whose components outside $S$ lie in the local integral set, and $W(t) = 0$ as soon as some component of $t$ outside $S$ fails to be integral, one has $\int W \, d\tau_G(u,z) = c_T \,(\int W_a \, d\tau_A(u,z)) \prod_{v \in S} \int W_{S,v} \, d\tau_F(u,z,v)$.
--
--   **Idelic product measure.** Data $P_Z$ of type [`UnramifiedWhittaker.ProductMeasureData SK νZK`](def/UnramifiedWhittaker_ZetaIntegrand.html#L20) (a positive constant $P_Z.c$, a measure $P_Z.\nu_S$, a projection homomorphism $P_Z.\mathrm{projS}$, an order function $P_Z.\mathrm{ord}$, together with the structure's compatibility clauses: triviality of $\mathrm{projS}$ off $S_K$, the decomposition and Tonelli clauses for unit ideles outside finite sets of places, and measurability of those sets), with $P_Z.\mathrm{ord} =$ `Idele.ord K` (`hPo`), $P_Z.\mathrm{projS} =$ `Idele.partAt K SK` (`hPp`), and $\mathrm{ofReal}(P_Z.c) \cdot P_Z.\nu_S$ equal to the pushforward under `Idele.partAt K SK` of $\nu_{ZK}$ restricted to the subgroup of unit ideles outside $S_K$ (`hPν`).
--
--   **Unweighted orbital values on the $K$-side.** Families $I_A(u,z)$ and $I_F(u,z,v)$ with: for $u \ne 1$, $I_A(u,z)$ is an orbital integral of $f_{aK}$ at $\gamma_\infty(u,z)$ with respect to $\nu_A$ and $\tau_A(u,z)$, i.e. $I_A(u,z) = \int f_{aK}(x^{-1}\gamma_\infty x)\,w(x)\,d\nu_A$ for some admissible section weight $w$ (`hIA`); and for $u \ne 1$ and $v \in S_K$, $I_F(u,z,v)$ is the corresponding orbital integral of $f_{S_K,v}$ at $\gamma_v(u,z)$ against the local Haar measure and $\tau_F(u,z,v)$ (`hIF`).
--
--   **Twisted side.** $L/K$ is Galois with $\sigma$ an automorphism whose integral powers exhaust $\mathrm{Gal}(L/K)$ (`hgen`) and $[L:K]$ prime (`hprime`); a homomorphism $\xi_L$ from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ with $\xi \circ (\text{idelic norm of the genuine base change } K \to L) = \xi_L$ for every $\xi \in \Xi$ (`hξN`); an archimedean test factor $\varphi_a$ for $L$ (`hφa`); functions $\varphi_{S,v}$ on $GL_2(L \otimes_K K_v)$ which for $v \in S_K$ are locally constant of compact support (`hφS`); the matching hypotheses `hmatchA`, that $\varphi_a \circ \mathrm{archIdentGL}$ and $f_{aK}$ are matching over $\mathbb{A}_{K,\infty}$ for $\sigma$ with respect to `archHaarL` and `archHaarK`, and `hmatchS`, that for $v \in S_K$ the pair $\varphi_{S,v}$, $f_{S_K,v}$ is matching over $K_v$ with respect to the semilocal and local Haar measures. Real constants $\kappa_{0L}, \kappa_L, c_G', c_T', C$ with $c_G', c_T', C > 0$.
--
--   **Weighted and twisted weighted values.** Families $J_A(u,z)$, $J_F(u,z,v)$ with, for $u \ne 1$, $J_A(u,z)$ a weighted orbital integral of $f_{aK}$ at $\gamma_\infty(u,z)$ against $\nu_A$ and $\tau_A(u,z)$ for the weight $y \mapsto -\log \mathrm{archHeight}_K(y) - \log \mathrm{archHeight}_K(w_\infty y)$, $w$ the adelic Weyl element (`hJA`), and, for $v \in S_K$, $J_F(u,z,v)$ the local weighted orbital integral of $f_{S_K,v}$ for the local weight (`hJF`). A measure $\nu_A'$ on $GL_2(L \otimes_K \mathbb{A}_{K,\infty})$, with $\nu_A =$ `archHaarK` (`hνA`) and $\nu_A' =$ `archHaarL` (`hνA'`). Elements $\delta_A(u,z)$ of $GL_2(L \otimes_K \mathbb{A}_{K,\infty})$ such that, for $u \ne 1$, if $\gamma_\infty(u,z)$ admits a norm then the norm string of $\delta_A(u,z)$ (the product of the first $[L:K]$ iterates of the $\sigma$-twist applied to $\delta_A(u,z)$) equals the image of $\gamma_\infty(u,z)$ under `toTensorGL` (`hδA`); measures $\tau_A'(u,z)$ on the $\sigma$-twisted centraliser $\{t : t\,\delta_A(u,z)\,\sigma(t)^{-1} = \delta_A(u,z)\}$, Haar for $u \ne 1$ (`hτA'`) and, for $u \ne 1$ and $\gamma_\infty(u,z)$ a norm, coupled with $\tau_A(u,z)$ through the conjugator $1$, i.e. the pushforward of $\tau_A'(u,z)$ under conjugation by $1$ coincides with the pushforward of $\tau_A(u,z)$ under `toTensorGL` (`hτA'c`); likewise elements $\delta_F(u,z,v)$ with the norm-string identity at $v \in S_K$ (`hδF`) and measures $\tau_F'(u,z,v)$ on the twisted centralisers, Haar for $u \ne 1$ (`hτF'`) and of mass $1$ on the preimage of the semilocal integral set (`hτF'1`). Finally $J_A'(u,z)$, equal for $u \ne 1$ and $\gamma_\infty(u,z)$ a norm to a twisted weighted orbital integral of $\varphi_a \circ \mathrm{archIdentGL}$ at $\delta_A(u,z)$ against $\nu_A'$ and $\tau_A'(u,z)$ for the weight $y \mapsto -\log \mathrm{archHeight}_L(\mathrm{archIdentGL}\,y) - \log \mathrm{archHeight}_L(w_{L,\infty}\cdot \mathrm{archIdentGL}\,y)$ (`hJA'`), and equal to $0$ when $\gamma_\infty(u,z)$ is not a norm (`hJA'0`); and $J_F'(u,z,v)$, for $v \in S_K$ the twisted weighted local orbital integral of $\varphi_{S,v}$ at $\delta_F(u,z,v)$ against $\tau_F'(u,z,v)$ and the semilocal weight when a norm exists (`hJF'`), and $0$ otherwise (`hJF'0`).
--
--   **Conclusion.** Under these hypotheses there exist natural numbers $A, q$ and an additive subgroup $\Lambda$ of $\mathbb{R}^r \times \mathbb{Z}^m$ such that $\Lambda$ carries the discrete topology, and:
--
--   1. there are an $\mathbb{R}$-linear functional $sl$ on $\mathbb{R}^r$ and a vector $\omega \in \mathbb{R}^m$ with $\omega \ne 0$ and $sl(\gamma_1) = \sum_i \omega_i \gamma_{2,i}$ for every $\gamma \in \Lambda$;
--
--   2. there are an additive homomorphism $\chi : \Lambda \to (\mathbb{R}/\mathbb{Z})^{r+m}$ and a map $\mathrm{lift} : \mathbb{R}^r \times \mathbb{Z}^m \to \mathbb{R}^{r+m}$ such that for $\gamma \in \Lambda$ and every index $j$ the class of $\mathrm{lift}(\gamma)_j$ in $\mathbb{R}/\mathbb{Z}$ equals $\chi(\gamma)_j$;
--
--   3. there are index maps $kC : \{1,\dots,r+m\} \to \{1,\dots,r\}$ and $kR : \{1,\dots,q\} \to \{1,\dots,r\}$ and families of complex-valued functions $B_w(a)$, $C_w(a,k)$, $E_w(a,j)$ on $\mathbb{R}^r \times \mathbb{R}^{r+m}$, indexed by $a < A$, $k < q$, $j < r+m$, all of them infinitely differentiable and all invariant under translation of the second argument by each standard basis vector: $B_w(a)(p_1, p_2 + e_j) = B_w(a)(p)$, and likewise for every $C_w(a,k)$ and every $E_w(a,j')$;
--
--   4. there is a compact set $S_x \subseteq \mathbb{R}^r$ such that $B_w(a)(p) = 0$, $C_w(a,k)(p) = 0$ for all $k$ and $E_w(a,j)(p) = 0$ for all $j$ whenever $p_1 \notin S_x$;
--
--   5. there is a sequence $i \mapsto \mathrm{sub}_i$ of additive subgroups of $\mathbb{R}^r \times \mathbb{Z}^m$, each contained in $\Lambda$;
--
--   6. there are maps $\mathrm{shape} : \mathbb{N} \to \{0,\dots,A-1\}$ and $\mathrm{lam} : \mathbb{N} \to \mathbb{C}$ with $\sum_i \|\mathrm{lam}_i\|$ summable;
--
--   7. there are sequences $x_0 : \mathbb{N} \to \mathbb{R}^r$, $n_0 : \mathbb{N} \to \mathbb{Z}^m$ and $\theta_0 : \mathbb{N} \to \mathbb{R}^{r+m}$,
--
--   such that for every $n \in \mathbb{Z}^m$ the following identity holds. Its left-hand side is the constant $(c_G' (c_T')^{-1}) \kappa_{0L} \kappa_L (C \cdot P_Z.c)/|\Xi|$ times the finitely supported sum (`finsum`) over the set of $u \in K^\times$ with $u \ne 1$, with $\mathrm{ord}_v$ of the principal idele of $u$ vanishing for every finite place $v \notin S_K \cup T$, and with $\mathrm{ord}_{v_i}$ of that idele equal to $f_{v_i} n_i$ for each $i < m$, where $v_i$ is the $i$-th element of $T$ under `T.equivFin`, of
--   $$\Big(\prod_{i} \big(\sqrt{Nw(v_i)}\, s(v_i)\big)^{-n_i}\Big) \cdot \Big(\text{$\|\mathrm{partAt}_{S_K}(u-1)\|$ if } u - 1 \ne 0,\ \text{else } 0\Big) \cdot \sum_{\xi \in \Xi} \int \xi(z_S) \,\mathcal{B}(u,z_S)\, dP_Z.\nu_S,$$
--   where $\|\cdot\|$ is the idelic norm `TateGlobal.ideleNorm` of the $S_K$-part of the principal idele of $u-1$, and
--   $$\mathcal{B}(u,z_S) = \big(J_A'(u,z_S) - [L:K]\,J_A(u,z_S)\big) \prod_{v \in S_K} I_F(u,z_S,v) + I_A(u,z_S) \sum_{v \in S_K} \big(J_F'(u,z_S,v) - [L:K]\,J_F(u,z_S,v)\big) \prod_{v' \in S_K \setminus \{v\}} I_F(u,z_S,v').$$
--   Its right-hand side is
--   $$\sum_{i=0}^{\infty} \mathrm{lam}_i \sum_{\gamma \in \mathrm{sub}_i} \begin{cases} \mathcal{W}_i(\gamma) & \text{if } \gamma_2 + n_{0,i} = n,\\ 0 & \text{otherwise},\end{cases}$$
--   both sums being unconditional sums of families (`tsum`), where, writing $x = x_{0,i} + \gamma_1 \in \mathbb{R}^r$ and $\theta = \theta_{0,i} + \mathrm{lift}(\gamma) \in \mathbb{R}^{r+m}$,
--   $$\mathcal{W}_i(\gamma) = B_w(\mathrm{shape}_i)(x,\theta) + \sum_{k<q} \big|1 - e^{x(kR\,k)}\big| \, C_w(\mathrm{shape}_i,k)(x,\theta) + \sum_{j<r+m} \Big(\|1 - e^{z_j}\|^2 \log \|1 - e^{z_j}\|\Big) E_w(\mathrm{shape}_i,j)(x,\theta),$$
--   with $z_j = x(kC\,j)/2 + 2\pi i\,\theta_j \in \mathbb{C}$, the real factors being coerced into $\mathbb{C}$.
--
--   This is the passage, on the unweighted side of the twisted (base-change) comparison, from the windowed discrepancy class sums of $GL_2$ over $K$ — sums over rational conjugacy classes $\mathrm{diag}(u,1)$ with prescribed orders at the primes of $T$ — to absolutely convergent combinations of twisted lattice sums of finitely many smooth kink windows on $\mathbb{R}^r \times (\mathbb{R}/\mathbb{Z})^{r+m}$. It is used by [`AutomorphicForm.exists_windingDatum_forall_coeff_eq_window_classSum_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted`](thm.html#AutomorphicForm.exists_windingDatum_forall_coeff_eq_window_classSum_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted) to package the resulting coefficient array as a winding datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

theorem AutomorphicForm.exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞc : ∀ ξ ∈ Ξ, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hΞt : ∀ ξ ∈ Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK) (hT2 : 2 ≤ T.card)

    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNw : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal = Nw v)
    (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          AutomorphicForm.SatakeCombination.slotDeg K L ws v = ζ v)

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (κ₀K κK : ℝ)

    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))

    (cτK : ℝ) (hcτK : 0 < cτK)
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
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        (u : K) ≠ 1 →
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

    (PZ : UnramifiedWhittaker.ProductMeasureData SK νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K SK)
    (hPν : ENNReal.ofReal PZ.c • PZ.νS = Measure.map (NumberField.Idele.partAt K SK)
      (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ↑SK)))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))

    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξN : ∀ ξ ∈ Ξ, ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)

    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ SK, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))
    (hmatchA : AutomorphicForm.AreMatchingArch K L σ φa faK)
    (hmatchS : ∀ v ∈ SK, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fSK v))

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
    (hδA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (δA u z) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z)))
    (hτA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τA' u z).IsHaarMeasure)
    (hτA'c : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (δA u z) 1 (τA u z) (τA' u z))
    (δF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.normString K L (v.adicCompletion K) σ (δF u z v) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF u z v)))
    (hτF' : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → (τF' u z v).IsHaarMeasure)
    (hτF'1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (JA' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ νA'
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
        (δA u z) (τA' u z) (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u z))
    (hJA'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) → JA' u z = 0)
    (JF' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF u z v) (τF' u z v) (φS v) (JF' u z v))
    (hJF'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      JF' u z v = 0) :
    ∃ (A q : ℕ) (Λ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), DiscreteTopology Λ ∧
      ∃ (sl : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ) (ω : Fin T.card → ℝ), ω ≠ 0 ∧
        (∀ γ ∈ Λ, sl γ.1 = ∑ i, ω i * (γ.2 i : ℝ)) ∧
      ∃ (χ : Λ →+ (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → AddCircle (1 : ℝ)))
        (lift : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)),
        (∀ (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) (hγ : γ ∈ Λ) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∃ (kC : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → Fin (Fintype.card (NumberField.InfinitePlace K))) (kR : Fin q → Fin (Fintype.card (NumberField.InfinitePlace K)))
        (Bw : Fin A → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ) (Cw : Fin A → Fin q → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ) (Ew : Fin A → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ),
        (∀ a, ContDiff ℝ (⊤ : ℕ∞) (Bw a)) ∧ (∀ a k, ContDiff ℝ (⊤ : ℕ∞) (Cw a k)) ∧ (∀ a j, ContDiff ℝ (⊤ : ℕ∞) (Ew a j)) ∧
        (∀ (a : Fin A) (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          Bw a (p.1, p.2 + Pi.single j 1) = Bw a p ∧ (∀ k, Cw a k (p.1, p.2 + Pi.single j 1) = Cw a k p) ∧
            ∀ j', Ew a j' (p.1, p.2 + Pi.single j 1) = Ew a j' p) ∧
      ∃ (Sx : Set (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)), IsCompact Sx ∧
        (∀ (a : Fin A) (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)), p.1 ∉ Sx → Bw a p = 0 ∧ (∀ k, Cw a k p = 0) ∧ ∀ j, Ew a j p = 0) ∧
      ∃ (sub : ℕ → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), (∀ i, sub i ≤ Λ) ∧
      ∃ (shape : ℕ → Fin A) (lam : ℕ → ℂ), (Summable fun i => ‖lam i‖) ∧
      ∃ (x₀ : ℕ → Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) (n₀ : ℕ → Fin T.card → ℤ) (θ₀ : ℕ → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
      ∀ n : Fin T.card → ℤ,
          (((cG' * cT'⁻¹ : ℝ) : ℂ) * (κ₀L : ℂ) * ((κL : ℝ) : ℂ) * ((C * PZ.c : ℝ) : ℂ) / (Ξ.card : ℂ)) *
          ∑ᶠ u ∈ {u : Kˣ | (u : K) ≠ 1 ∧
              (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) ∧
              ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
                (AutomorphicForm.SatakeCombination.slotDeg K L ws (T.equivFin.symm i).1 : ℤ) * n i},
            (∏ i : Fin T.card, (((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ (-(n i)))) *
            (if h1 : (u : K) - 1 ≠ 0 then
                ((NumberField.TateGlobal.ideleNorm K
                    (NumberField.Idele.partAt K SK (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
              else 0) *
            ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
                ((JA' u zS - (Module.finrank K L : ℂ) * JA u zS) * ∏ v ∈ SK, IF u zS v +
                  IA u zS * ∑ v ∈ SK, (JF' u zS v - (Module.finrank K L : ℂ) * JF u zS v) * ∏ v' ∈ SK.erase v, IF u zS v') ∂PZ.νS =
        ∑' i : ℕ, lam i * ∑' γ : sub i,
          if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ i = n then
            Bw (shape i) (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ k : Fin q, ((|1 - Real.exp ((x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kR k))| : ℝ) : ℂ) * Cw (shape i) k (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card), ((‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ ^ 2 *
                    Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
                Ew (shape i) j (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
          else 0 := by sorry
