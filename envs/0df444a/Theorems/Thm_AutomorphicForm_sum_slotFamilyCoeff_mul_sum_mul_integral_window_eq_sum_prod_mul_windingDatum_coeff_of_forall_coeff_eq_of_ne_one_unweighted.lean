-- Prove2me | Theorems.Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted
-- name    : AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/3ba752c2-d41d-58db-8078-5492fefba696
-- title:
--   Unweighted window class sums as a winding pairing
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, $\mathbb{A}_K$ denotes `AdeleRing (𝓞 K) K`, and for $u\in K^\times$ and an idele class $z\in\mathbb{A}_K^\times$ the symbol $\gamma(u,z)$ abbreviates the element [`AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) 1`](def/AutomorphicForm_AdelicLsXi.html#L18) of $\mathrm{GL}_2(\mathbb{A}_K)$, i.e. the scalar matrix $z\cdot 1$ times $\mathrm{diag}(u,1)$; `AdelicLevel.glArch` and `AdelicLevel.finComponent … (AdelicLevel.glFin …)` denote its archimedean component and its component at a finite place $v$.
--
--   **Places and Galois data.** A system `ws` assigns to every $v\in\mathrm{HeightOneSpectrum}(𝓞 K)$ a prime `(ws v).1` of $𝓞 L$ lying under $v$; `SK` and `T` are finite sets of finite places of $K$ with `hTS : Disjoint T SK`. Later, $L/K$ is assumed Galois with $\sigma$ an automorphism such that every $\tau\in\mathrm{Gal}(L/K)$ lies in `Subgroup.zpowers σ` (`hgen`), and `hprime` requires $[L:K]$ to be prime.
--
--   **Characters.** $\Xi$ is a finite set of homomorphisms $(\mathbb{A}_K^\times)\to\mathbb{C}^\times$ (written on the full subgroup $\top$); `hΞc` asserts continuity of each, `hΞt` triviality on the image of $K^\times$, and `hur` that each $\xi\in\Xi$ is trivial on the idele of a local unit $t$ at any $v\notin SK$ with $\mathrm{v}(t)=1$. A character $\xi_L$ of $(\mathbb{A}_L^\times)$ is given with `hξN`: each $\xi\in\Xi$ pulled back along the idelic norm of `(M4aHerbrand.GenuineDescent.genuineBaseChange K L)` equals $\xi_L$.
--
--   **Local Hecke data at $T$.** Elements `ϖKs v` of the valuation ring at $v$ are irreducible with nonzero image in $K_v$ for $v\in T$ (`hϖKi`, `hϖKs0`); `rKs v : Fin (nKs v) → GL₂(K_v)` is, by `hrKs`, a Hecke coset system ([`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15)) for the subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) of $K_v$-points coming from the valuation ring and for the element [`LocalGL2.diagPi (ϖKs v)`](def/LocalLanglands_HeckeCosetLocal.html#L68), i.e. the representatives lie in the double coset, cover it modulo the subgroup, and are pairwise inequivalent; `hzKs` says that `zKs v` is the scalar matrix $\varpi_v\cdot 1$ for $v\in T$. Natural numbers `ks`, `js` fix the Hecke word.
--
--   **Satake normalisations.** `hNw` and `hNwf` state, for $v\in T$, that $Nw(v)$ is the absolute norm of the ideal `(ws v).1.asIdeal` and equals $(\mathrm{absNorm}\,v)^{f_v}$ with $f_v=$ [`AutomorphicForm.SatakeCombination.slotDeg K L ws v`](def/AutomorphicForm_SatakeCombinationCoeff.html#L20), the inertia degree of `(ws v).1` over $v$. Complex numbers $\zeta_v\ne 0$ and $s_v$ satisfy $s_v^2=\zeta_v$ for $v\in T$ (`hζ`, `hs`), and `hx` requires $\xi(\det(\mathrm{heckeGen}_v))^{f_v}=\zeta_v$ for all $\xi\in\Xi$ and $v\in T$.
--
--   **Test functions on the $K$-side.** `faK` is an archimedean test factor (`IsArchTestFactor`: given by a $C^\infty$ function of the matrix entries in the mixed space, with compact support) and, for $v\in SK$, `fSK v` is a locally constant compactly supported function on $\mathrm{GL}_2(K_v)$ (`IsLocalTestFn`).
--
--   **Diagonal class representatives.** $\Delta_K$ is a finite set of elements of $\mathrm{GL}_2(K)$ which are diagonal with ratio $\gamma_{00}/\gamma_{11}\ne 1$ (`hΔK`), the ratio map being injective on $\Delta_K$ (`hΔKinj`); `uK`, `dK` are maps to $K^\times$ whose values on $\Delta_K$ are the ratio $\gamma_{00}/\gamma_{11}$ and the entry $\gamma_{11}$ respectively (`huK`, `hdK`).
--
--   **Measure factorisations.** `νA` is a measure on $\mathrm{GL}_2$ of the infinite adeles for the Borel structure `glBorelOf`, and `hG` (with constant `cG`) asserts: for every finite set $S$ of places and every $f$, $f_\infty$, $(f_v)$ with the stated measurability, such that $f$ factorises as $f_\infty$ times $\prod_{v\in S} f_v$ on those $g$ whose components off $S$ lie in `localIntegralSet`, and vanishes when some component off $S$ leaves that set, the integral of $f$ against `adelicGLHaar` equals $cG\cdot\int f_\infty\,d\nu_A\cdot\prod_{v\in S}\int f_v\,d(\mathrm{localHaar})$. For each $u,z$, `τG u z` is a measure on the centraliser of $\gamma(u,z)$ in $\mathrm{GL}_2(\mathbb{A}_K)$, Haar when $u\ne 1$ (`hτG`), and `hτGc` (constant $c_{\tau K}>0$) computes its integrals as $c_{\tau K}$ times the integral of $g(\mathrm{diag}(p_1,p_2))$ over $\mathbb{A}_K^\times\times\mathbb{A}_K^\times$ for $\nu_{ZK}\times\nu_{ZK}$. Likewise `τA u z` and `τF u z v` are measures on the centraliser of the archimedean, resp. the $v$-component, of $\gamma(u,z)$, Haar for $u\ne 1$ (`hτA`, `hτF`), with `hτF1` normalising the mass of the preimage of `localIntegralSet K v` to $1$; `hT` (constant $c_T>0$) is the corresponding factorisation of integrals over the adelic centraliser into archimedean and local centraliser integrals.
--
--   **Idele product measure data.** `PZ : UnramifiedWhittaker.ProductMeasureData SK νZK` carries a positive constant `PZ.c`, a measure `PZ.νS`, a projection `PZ.projS`, an order function `PZ.ord`, and the decomposition and Tonelli clauses of that structure; `hPo`, `hPp` identify `PZ.ord` with [`NumberField.Idele.ord K`](def/NumberField_IdeleProductMeasure.html#L13) and `PZ.projS` with [`NumberField.Idele.partAt K SK`](def/NumberField_IdeleProductMeasure.html#L90), and `hPν` states that $\mathrm{ofReal}(PZ.c)\cdot PZ.\nu_S$ is the pushforward under `partAt K SK` of $\nu_{ZK}$ restricted to the unit ideles outside $SK$.
--
--   **Orbital integrals.** For $u\ne 1$: `IA u z` is an orbital integral of `faK` at the archimedean component of $\gamma(u,z)$ for `τA u z` and `νA` (`hIA`), and `IF u z v` an orbital integral of `fSK v` at the $v$-component for $v\in SK$ (`hIF`); `JA u z` is a weighted orbital integral of `faK` with weight $y\mapsto -\log \mathrm{archHeight}_K(y)-\log \mathrm{archHeight}_K(w_\infty y)$, $w$ the adelic Weyl element (`hJA`), and `JF u z v` the corresponding weighted local orbital integrals at $v\in SK$ (`hJF`).
--
--   **$L$-side data, matching, and twisted integrals.** `φa` is an archimedean test factor for $L$ and, for $v\in SK$, `φS v` a locally constant compactly supported function on $\mathrm{GL}_2(L\otimes_K K_v)$ (`IsSemiLocalTestFn`); `hmatchA`, `hmatchS` assert the matching relations `AreMatchingArch` and `AreMatchingLocal` between these and `faK`, `fSK`. The measure `νA'` on $\mathrm{GL}_2(L\otimes_K \mathbb{A}_{K,\infty})$ and `νA` are normalised by `hνA`, `hνA'` to be `archHaarK K` and `archHaarL K L`. Elements `δA u z`, `δF u z v` satisfy, whenever a norm of the relevant component exists, that their norm string $\delta\,\sigma\delta\cdots\sigma^{[L:K]-1}\delta$ equals the image of that component under `toTensorGL` (`hδA`, `hδF`); `τA'`, `τF'` are Haar measures on the $\sigma$-twisted centralisers of `δA u z`, `δF u z v` (`hτA'`, `hτF'`), `hτF'1` normalising the mass of the preimage of `semiLocalIntegralSet K L v` to $1$, and `hτA'c` asserting the coupling relation `Coupled … 1 (τA u z) (τA' u z)`, i.e. that `τA'` and `τA` push forward to the same measure on $\mathrm{GL}_2(L\otimes_K\mathbb{A}_{K,\infty})$. Then `JA' u z` is a twisted weighted orbital integral of $\varphi_a\circ$ `archIdentGL` at `δA u z` with the weight $y\mapsto-\log\mathrm{archHeight}_L(\mathrm{archIdentGL}\,y)-\log\mathrm{archHeight}_L(w_{L,\infty}\,\mathrm{archIdentGL}\,y)$ (`hJA'`), vanishing when no norm exists (`hJA'0`), and `JF' u z v` the twisted weighted local analogues at $v\in SK$, again vanishing in the absence of a norm (`hJF'`, `hJF'0`).
--
--   **Hecke-word and unramified local integrals.** For $m$ in [`AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T`](def/AutomorphicForm_SatakeCombinationCoeff.html#L32) (the product over $v\in T$ of the supports of the slot words), $u\ne 1$ and $v\in T$, `IW m u z v` is an orbital integral at the $v$-component of $\gamma(u,z)$ of the function $x\mapsto\sum_{\iota:\mathrm{Fin}(m_v(0))\to\mathrm{Fin}(nKs\,v)}\mathbf{1}_{\mathrm{localIntegralSet}}\big((\prod_i rKs_v(\iota_i)\cdot (zKs\,v)^{m_v(1)})^{-1}x\big)$ (`hIW`); for $v\notin SK\cup T$, `IU u z v` is an orbital integral of the indicator of `localIntegralSet K v` (`hIU`).
--
--   **The window integrand.** For $m$ in the slot index, $\gamma\in\Delta_K$ and $z$, `hWK` prescribes
--   $$W_K(m,\gamma,z)=\Big(\prod_{v\in T}IW\,m\,u_\gamma\,z'\,v\Big)\Big(\prod^{\mathrm f}_{v\notin SK\cup T}IU\,u_\gamma\,z'\,v\Big)\Big[(JA'-[L:K]\,JA)\prod_{v\in SK}IF_v+IA\sum_{v\in SK}(JF'_v-[L:K]\,JF_v)\prod_{v'\in SK\setminus\{v\}}IF_{v'}\Big],$$
--   all integrals being taken at $u_\gamma=uK\,\gamma$ and $z'=z\cdot d_K\gamma$ (image of $dK\,\gamma$ in the ideles), the second product being a `finprod`. The hypothesis `hΔKc` states that the same bracketed product vanishes for every $m$ in the slot index, every $u\in K^\times$ with $u\ne1$ whose ratio is attained by no $\gamma\in\Delta_K$, and every $z$.
--
--   **Winding datum.** Finally $r,c\in\mathbb{N}$ and $\mathcal B$ is a [`AutomorphicForm.WindingDatum r T.card c`](def/AutomorphicForm_WindingDatum.html#L11), and `hℬ` requires that for every $n:\mathrm{Fin}\,|T|\to\mathbb{Z}$ the coefficient $\mathcal B.\mathrm{coeff}\,n$ equal
--   $$\frac{cG'\,cT'^{-1}\,\kappa_0^L\,\kappa^L\,(C\cdot PZ.c)}{|\Xi|}\sum_{u}^{\mathrm f}\Big(\prod_i(\sqrt{Nw_i}\,s_i)^{-n_i}\Big)\cdot\Big(\text{if }u-1\ne0\text{ then }\|\mathrm{partAt}_{SK}(u-1)\|_{\mathbb{A}}\text{ else }0\Big)\cdot\sum_{\xi\in\Xi}\int \xi(z_S)\,B(u,z_S)\,dPZ.\nu_S,$$
--   where the `finsum` runs over the $u\in K^\times$ with $u\ne1$, $\mathrm{ord}_v(u)=0$ for all $v\notin SK\cup T$, and $\mathrm{ord}_{v_i}(u)=f_{v_i}\,n_i$ at the $i$-th place $v_i=$ `T.equivFin.symm i` of $T$; the index $i$ runs over $\mathrm{Fin}\,|T|$ with $Nw_i$, $s_i$ taken at $v_i$; $\|\cdot\|_{\mathbb{A}}$ is [`NumberField.TateGlobal.ideleNorm K`](def/NumberField_TateGlobalZeta.html#L19); and $B(u,z_S)$ is the bracket $(JA'-[L:K]JA)\prod_{v\in SK}IF_v+IA\sum_{v\in SK}(JF'_v-[L:K]JF_v)\prod_{v'\in SK\setminus\{v\}}IF_{v'}$ evaluated at $(u,z_S)$. Positivity is assumed for $cG'$, $cT'$ and $C$ (`hcG'`, `hcT'`, `hC`), while $\kappa_0^L$ and $\kappa^L$ are arbitrary reals.
--
--   **Conclusion.** Under these hypotheses,
--   $$\frac{cG'\,cT'^{-1}\,\kappa_0^L\,\kappa^L\,C}{|\Xi|}\sum_{m\in\mathrm{slotIndex}}\mathrm{slotFamilyCoeff}(m)\sum_{\gamma\in\Delta_K}\sum_{\xi\in\Xi}\int_{\mathbb{A}_K^\times}\xi(z)\,W_K(m,\gamma,z)\,d\nu_{ZK}(z)$$
--   equals
--   $$\sum_{n}\ \Big(\prod_{i}(\sqrt{Nw_i}\,s_i)^{k_{v_i}}\,\zeta_{v_i}^{\,j_{v_i}}\cdot\big[(T+T^{-1})^{k_{v_i}}\big]_{n_i}\Big)\cdot\mathcal B.\mathrm{coeff}\,n,$$
--   the sum being over $n$ in the box $\prod_{i}[-k_{v_i},k_{v_i}]$ (`Fintype.piFinset` of the intervals `Finset.Icc`), $[\,\cdot\,]_{n_i}$ denoting the coefficient at $n_i$ of the indicated power of $T+T^{-1}$ in `LaurentPolynomial ℂ`, $v_i=$ `T.equivFin.symm i`, and $\mathrm{slotFamilyCoeff}(m)=\prod_{v\in T}\mathrm{slotCoeff}\,v\,(k_v)\,(j_v)\,(m_v)$.
--
--   This is the packaging step for the intercept, or window, contribution to the hyperbolic part of the base-change comparison for $\mathrm{GL}(2)$ along a Hecke word: the class sums over the diagonal representatives $\Delta_K$, taken unweighted over all ratios $u\neq1$, are rewritten as a pairing of the Satake–Laurent coefficients of $(T+T^{-1})^{k_v}$ against the coefficient array of a winding datum. It is used by [`AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff`](thm.html#AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_windowClassIntegral_eq_sum_satakeLaurent_mul_coeff), which produces such a winding datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted.lean

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

theorem AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted
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
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK)

    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hϖKi : ∀ v ∈ T, Irreducible (ϖKs v))
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
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)

    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNw : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal = Nw v)
    (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ AutomorphicForm.SatakeCombination.slotDeg K L ws v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          AutomorphicForm.SatakeCombination.slotDeg K L ws v = ζ v)

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))

    (ΔK : Finset (GL (Fin 2) K))
    (hΔK : ∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (hΔKinj : ∀ γ ∈ ΔK, ∀ γ' ∈ ΔK,
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 =
        (γ' : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ' : Matrix (Fin 2) (Fin 2) K) 1 1 → γ = γ')

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
      JF' u z v = 0)

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

    (r c : ℕ) (ℬ : AutomorphicForm.WindingDatum r T.card c)
    (hℬ : ∀ n : Fin T.card → ℤ, ℬ.coeff n =
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
                IA u zS * ∑ v ∈ SK, (JF' u zS v - (Module.finrank K L : ℂ) * JF u zS v) * ∏ v' ∈ SK.erase v, IF u zS v') ∂PZ.νS) :
    (((cG' * cT'⁻¹ : ℝ) : ℂ) * (κ₀L : ℂ) * ((κL : ℝ) : ℂ) * ((C : ℝ) : ℂ) / (Ξ.card : ℂ)) *
      ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∑ γ ∈ ΔK,
              ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * WK m γ z ∂νZK =
      ∑ n ∈ Fintype.piFinset (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
        (∏ i : Fin T.card,
            ((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 * ζ (T.equivFin.symm i).1 ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) *
          ℬ.coeff n := by sorry
