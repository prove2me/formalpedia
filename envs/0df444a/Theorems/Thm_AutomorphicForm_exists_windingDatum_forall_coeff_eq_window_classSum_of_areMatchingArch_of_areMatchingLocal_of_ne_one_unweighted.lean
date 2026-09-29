-- Prove2me | Theorems.Thm_AutomorphicForm_exists_windingDatum_forall_coeff_eq_window_classSum_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted
-- name    : AutomorphicForm.exists_windingDatum_forall_coeff_eq_window_classSum_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/2476528f-3d7b-53e5-9810-a79fc4b9a52b
-- title:
--   Winding-datum realisation of the unweighted window class sum
-- statement:
--   Fix number fields $K$ and $L$ with $L$ a $K$-algebra, and a function `ws` assigning to every finite place $v$ of $K$ a prime of $\mathcal{O}_L$ lying over $v$ (an element of `v.Extension (𝓞 L)`). Fix a Haar measure $\nu_{Z,K}$ on the idele unit group $(\mathbb{A}_K)^\times$ for a Borel measurable structure on that group.
--
--   **Characters.** $\Xi$ is a finite set of homomorphisms from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, subject to: `hΞc`, each $\xi \in \Xi$ is continuous as a $\mathbb{C}$-valued function of the idele; `hΞt`, each $\xi \in \Xi$ is trivial on the image of $K^\times$; and, after two finite sets $S_K, T$ of finite places of $K$ are fixed with `hTS` $T$ disjoint from $S_K$ and `hT2` $|T| \ge 2$, the hypothesis `hur`: for $\xi \in \Xi$, $v \notin S_K$ and $t \in (K_v)^\times$ with $|t|_v = 1$, the value of $\xi$ at the idele which is $t$ at $v$, $1$ at all other finite places and $1$ archimedean (built by `localUnit` followed by `finIncl`) is $1$.
--
--   **Satake data at $T$.** A function $N_w$ on finite places with `hNw`: $N_w(v)$ is the absolute norm of the ideal $(\mathrm{ws}\,v)$ for $v \in T$; `hNwf`: $N_w(v) = (\mathrm{absNorm}\, v)^{f_v}$ for $v \in T$, where $f_v =$ `SatakeCombination.slotDeg K L ws v` is the inertia degree `v.asIdeal.inertiaDeg'` of the chosen prime above $v$. Complex functions $\zeta, s$ on finite places with `hζ`: $\zeta_v \ne 0$ on $T$; `hs`: $s_v^2 = \zeta_v$ on $T$; `hx`: for $\xi \in \Xi$ and $v \in T$, $\xi(\det \mathrm{heckeGen}_v)^{f_v} = \zeta_v$.
--
--   **Test functions and measures on the $K$-side.** $f_{a,K}$ on $\mathrm{GL}_2$ of the infinite adele ring of $K$ with `hfaK`: $f_{a,K} = \Phi \circ \mathrm{archEntries}$ for some $C^\infty$ function $\Phi$ of the matrix of archimedean entries, and $f_{a,K}$ has compact support. Functions $f_{S_K,v}$ on $\mathrm{GL}_2(K_v)$ with `hfSK`: for $v \in S_K$ they are locally constant with compact support. Real constants $\kappa_{0,K}, \kappa_K$. A measure $\nu_A$ on $\mathrm{GL}_2$ of the infinite adele ring for the Borel structure `glBorelOf`.
--
--   For $u \in K^\times$ and $z \in (\mathbb{A}_K)^\times$ write $\gamma(u,z) = z \cdot \mathrm{diag}(u,1)$, the product of the central scalar matrix attached to $z$ and the diagonal matrix `diagUnits2` of the image of $u$ and $1$, an element of $\mathrm{GL}_2(\mathbb{A}_K)$. The measure data are: $\tau_G(u,z)$ on the centraliser of $\{\gamma(u,z)\}$, with `hτG` Haar whenever $u \ne 1$ and `hτGc` the normalisation that for $u \ne 1$ and every $g : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, $\int_{Z(\gamma)} g = c_{\tau,K} \int\!\!\int g(\mathrm{diag}(p_1,p_2))\, d(\nu_{Z,K} \times \nu_{Z,K})$, where $c_{\tau,K} > 0$ by `hcτK`; $\tau_A(u,z)$ on the centraliser of the archimedean image $\mathrm{glArch}(\gamma(u,z))$ with `hτA` Haar for $u \ne 1$; and $\tau_F(u,z,v)$ on the local centraliser of the $v$-component of the finite image $\mathrm{glFin}(\gamma(u,z))$, with `hτF` Haar for $u \ne 1$ and `hτF1` total mass $1$ on the preimage of the local integral set $\mathrm{localIntegralSet}\,K\,v$ (matrices with entries and inverse entries in $\mathcal{O}_{K_v}$), again for $u \ne 1$.
--
--   A constant $c_T > 0$ and the factorisation hypothesis `hT`: for all $u, z$, every finite set $S$ of finite places and all functions $W$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $W_a$ on the archimedean $\mathrm{GL}_2$ and $W_{S,v}$ on $\mathrm{GL}_2(K_v)$, if $u \ne 1$, if $W_a$ is almost everywhere strongly measurable for $\tau_A(u,z)$ and each $W_{S,v}$ ($v \in S$) for $\tau_F(u,z,v)$, if $W(t) = W_a(\mathrm{glArch}\,t)\prod_{v \in S} W_{S,v}(\mathrm{glFin}\,t)_v$ for every $t$ in the centraliser all of whose components outside $S$ lie in the local integral sets, and if $W(t) = 0$ for every $t$ having some component outside $S$ not in the local integral set, then $\int W \, d\tau_G(u,z) = c_T \cdot (\int W_a\, d\tau_A(u,z)) \cdot \prod_{v \in S} \int W_{S,v} \, d\tau_F(u,z,v)$.
--
--   **Idelic product measure.** $P_Z$ is a [`UnramifiedWhittaker.ProductMeasureData`](def/UnramifiedWhittaker_ZetaIntegrand.html#L20) for $S_K$ and $\nu_{Z,K}$, that is, a positive constant $P_Z.c$, a measure $P_Z.\nu_S$, a homomorphism $P_Z.\mathrm{projS}$ and an order function $P_Z.\mathrm{ord}$ satisfying the structure's axioms (support of the projection off $S_K$, a decomposition of unit ideles outside a finite set, a Tonelli-type identity for integrals of $f(\mathrm{projS}\,a)\prod_v \varphi_v(\mathrm{ord}_v a)$ with constant $P_Z.c$, and measurability of the relevant subgroups). It is pinned by `hPo`: $P_Z.\mathrm{ord} =$ `Idele.ord K`; `hPp`: $P_Z.\mathrm{projS} =$ `Idele.partAt K SK`; and `hPν`: $\mathrm{ofReal}(P_Z.c) \cdot P_Z.\nu_S$ is the pushforward under `Idele.partAt K SK` of $\nu_{Z,K}$ restricted to the unit ideles outside $S_K$.
--
--   **Unweighted orbital integrals.** $I_A(u,z)$ with `hIA`: for $u \ne 1$, $I_A(u,z)$ is an orbital integral of $f_{a,K}$ at $\mathrm{glArch}(\gamma(u,z))$ for $\nu_A$ and $\tau_A(u,z)$, i.e. $I_A(u,z) = \int f_{a,K}(x^{-1}\gamma x) w(x)\, d\nu_A$ for some nonnegative measurable compactly supported section weight $w$ with $\int_{Z(\gamma)} w(tx)\,d\tau_A = 1$ whenever $f_{a,K}(x^{-1}\gamma x) \ne 0$. $I_F(u,z,v)$ with `hIF`: for $u \ne 1$ and $v \in S_K$, the corresponding local orbital integral of $f_{S_K,v}$ at the $v$-component of $\mathrm{glFin}(\gamma(u,z))$ for the local Haar measure and $\tau_F(u,z,v)$.
--
--   **Cyclic base change data.** $L/K$ is Galois, $\sigma$ is an automorphism with `hgen`: every element of $\mathrm{Gal}(L/K)$ lies in the subgroup generated by $\sigma$, and `hprime`: $[L:K]$ is prime. $\xi_L$ is a homomorphism from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ with `hξN`: every $\xi \in \Xi$, composed with the idelic norm of `genuineBaseChange K L`, equals $\xi_L$. Test data on the $L$-side: $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adele ring of $L$ with `hφa` an arch test factor in the above sense; $\varphi_{S,v}$ on $\mathrm{GL}_2(L \otimes_K K_v)$ with `hφS` locally constant of compact support for $v \in S_K$; and the matching hypotheses `hmatchA`, that $\varphi_a \circ \mathrm{archIdentGL}$ and $f_{a,K}$ are matching for `archHaarL K L` and `archHaarK K` in the sense of `AreMatchingOn`, and `hmatchS`, that for $v \in S_K$ the pair $(\varphi_{S,v}, f_{S_K,v})$ is matching for the semi-local and local Haar measures.
--
--   **Constants and weighted integrals.** Reals $\kappa_{0,L}, \kappa_L, c_{G'}, c_{T'}, C$ with $c_{G'}, c_{T'}, C > 0$. $J_A(u,z)$ with `hJA`: for $u \ne 1$ it is the weighted orbital integral of $f_{a,K}$ at $\mathrm{glArch}(\gamma(u,z))$ for $\nu_A$ and $\tau_A(u,z)$, with weight $y \mapsto -\log \mathrm{archHeight}_K(y) - \log \mathrm{archHeight}_K(\mathrm{glArch}(\mathrm{adelicWeyl})\, y)$, where $\mathrm{archHeight}$ is the product over infinite places of the local heights raised to the place multiplicities; $J_F(u,z,v)$ with `hJF`: for $u \ne 1$, $v \in S_K$, the local weighted orbital integral of $f_{S_K,v}$ with the local weight. A measure $\nu_{A'}$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$, pinned by `hνA`: $\nu_A =$ `archHaarK K`, and `hνA'`: $\nu_{A'} =$ `archHaarL K L`.
--
--   Twisted data: $\delta_A(u,z) \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ with `hδA`: for $u \ne 1$, provided $\mathrm{glArch}(\gamma(u,z))$ admits a norm in the sense of `IsNormOf`, the norm string $\prod_{i<[L:K]} \sigma^i(\delta_A(u,z))$ equals the image of $\mathrm{glArch}(\gamma(u,z))$ under `toTensorGL`; measures $\tau_{A'}(u,z)$ on the twisted centraliser $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\delta_A(u,z)$, with `hτA'` Haar for $u \ne 1$ and `hτA'c` the coupling condition (`Coupled` with conjugator $1$): the pushforward of $\tau_{A'}(u,z)$ under $t \mapsto t$ coincides with the pushforward of $\tau_A(u,z)$ along `toTensorGL`, again under the hypothesis that a norm exists. Likewise $\delta_F(u,z,v)$ with `hδF` the corresponding norm-string identity at places $v \in S_K$, and $\tau_{F'}(u,z,v)$ on the twisted centraliser of $\delta_F(u,z,v)$ with `hτF'` Haar and `hτF'1` total mass $1$ on the preimage of the semi-local integral set (matrices with entries and inverse entries in the image of the tensor integers).
--
--   Finally the twisted weighted orbital integrals: $J_{A'}(u,z)$ with `hJA'`: for $u \ne 1$ and when $\mathrm{glArch}(\gamma(u,z))$ admits a norm, $J_{A'}(u,z) = \int \varphi_a(\mathrm{archIdentGL}(x^{-1}\delta_A \sigma(x)))\, \mathrm{wt}(x) s(x) \, d\nu_{A'}$ for some twisted section weight $s$, the weight being $y \mapsto -\log \mathrm{archHeight}_L(\mathrm{archIdentGL}\,y) - \log \mathrm{archHeight}_L(\mathrm{glArch}(\mathrm{adelicWeyl}_L)\,\mathrm{archIdentGL}\,y)$; and `hJA'0`: $J_{A'}(u,z) = 0$ when $u \ne 1$ and no norm exists. Similarly $J_{F'}(u,z,v)$ with `hJF'` the semi-local twisted weighted orbital integral of $\varphi_{S,v}$ at $\delta_F(u,z,v)$ for $\tau_{F'}(u,z,v)$ when a norm exists, and `hJF'0` its vanishing otherwise, both for $u \ne 1$ and $v \in S_K$.
--
--   **Conclusion.** There exists a winding datum $\mathcal{B}$ of signature $(r, d, c)$ with $r$ the number of infinite places of $K$, $d = |T|$ and $c = r + |T|$ — that is, a discrete lattice $\Lambda \le (\mathbb{R}^r) \times \mathbb{Z}^d$, a linear functional, a nonzero frequency vector $\omega$ compatible with $\Lambda$, a character of $\Lambda$ into $(\mathbb{R}/\mathbb{Z})^c$, subgroups of $\Lambda$, and integrable continuous profiles with quadratic decay bounds for them and their Fourier transforms, together with the remaining data of the structure — such that for every $n : \mathrm{Fin}\,|T| \to \mathbb{Z}$ the coefficient $\mathcal{B}.\mathrm{coeff}\, n$ equals
--   $$\frac{c_{G'} c_{T'}^{-1}\, \kappa_{0,L}\, \kappa_L\, (C \cdot P_Z.c)}{|\Xi|} \sum_{u}^{\mathrm{f}} \Bigl( \prod_{i} \bigl(\sqrt{N_w(v_i)}\, s(v_i)\bigr)^{-n_i} \Bigr) \cdot \| (u-1)_{S_K} \| \cdot \sum_{\xi \in \Xi} \int \xi(z_S) \, \mathcal{W}(u, z_S) \, dP_Z.\nu_S,$$
--   where the (finite-support) sum runs over the set of $u \in K^\times$ such that $u \ne 1$, $\mathrm{ord}_v$ of the principal idele of $u$ vanishes for every finite place $v \notin S_K \cup T$, and $\mathrm{ord}_{v_i}$ of that idele equals $f_{v_i} \cdot n_i$ for every $i$, with $v_i =$ `(T.equivFin.symm i).1` the enumeration of $T$ and $f_{v_i}$ the slot degree; the tilt factor is the product over $i$ of the integral powers $(\sqrt{N_w(v_i)}\,s(v_i))^{-n_i}$; the discriminant factor $\|(u-1)_{S_K}\|$ is, by the dependent case distinction, the real `TateGlobal.ideleNorm` of `Idele.partAt K SK` applied to the principal idele of the unit $u - 1$ when $u - 1 \ne 0$, and $0$ otherwise; and the window bracket is
--   $$\mathcal{W}(u,z_S) = \bigl(J_{A'}(u,z_S) - [L:K]\, J_A(u,z_S)\bigr)\prod_{v \in S_K} I_F(u,z_S,v) \; + \; I_A(u,z_S) \sum_{v \in S_K} \bigl(J_{F'}(u,z_S,v) - [L:K]\, J_F(u,z_S,v)\bigr) \prod_{v' \in S_K \setminus \{v\}} I_F(u,z_S,v').$$
--   The integration variable $z_S$ runs over $(\mathbb{A}_K)^\times$ against $P_Z.\nu_S$.
--
--   The statement packages the unweighted hyperbolic-window (discrepancy) class sum arising from the comparison of the weighted trace formulae for $\mathrm{GL}_2$ over $K$ and over a cyclic prime-degree extension $L$ into a single winding datum of the pinned signature $(r_1+r_2, |T|, r_1+r_2+|T|)$, so that its coefficient array in the $T$-exponents $n$ is exactly that class sum. It is used in the base-change step of the Langlands–Tunnell input, being cited by [`AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff`](thm.html#AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff), where the winding datum is paired with Satake Laurent expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_windingDatum_forall_coeff_eq_window_classSum_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted.lean

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

theorem AutomorphicForm.exists_windingDatum_forall_coeff_eq_window_classSum_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted
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
    ∃ ℬ : AutomorphicForm.WindingDatum (Fintype.card (NumberField.InfinitePlace K)) T.card
        (Fintype.card (NumberField.InfinitePlace K) + T.card), ∀ n : Fin T.card → ℤ, ℬ.coeff n =
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
                IA u zS * ∑ v ∈ SK, (JF' u zS v - (Module.finrank K L : ℂ) * JF u zS v) * ∏ v' ∈ SK.erase v, IF u zS v') ∂PZ.νS := by sorry
