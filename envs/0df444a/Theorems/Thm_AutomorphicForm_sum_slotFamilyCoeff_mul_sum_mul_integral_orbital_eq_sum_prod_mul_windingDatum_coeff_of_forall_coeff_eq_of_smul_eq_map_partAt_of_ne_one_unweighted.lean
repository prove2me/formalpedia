-- Prove2me | Theorems.Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted
-- name    : AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/a894b127-4f18-55fa-b600-8a57ada072a7
-- title:
--   Hyperbolic class sums of a Hecke word as winding pairing
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, and `ws` assigns to every finite place $v$ of $K$ a height-one prime $w =$ `ws v` of $\mathcal{O}_L$ lying under $v$. The idele unit group $(\mathbb{A}_K)^\times$ carries a measurable structure that is the Borel structure of its topology, and `νZK` is a Haar measure on it. On $\mathrm{GL}_2$ of the adeles the Haar measure `adelicGLHaar`, on $\mathrm{GL}_2(K_v)$ the measure [`AutomorphicForm.localHaar`](def/AutomorphicForm_LocalOrbitalBase.html#L168) normalised by the compact open subset [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) of matrices integral together with their inverses, and on $\mathrm{GL}_2$ of the infinite adeles and on the various centralisers the Borel structures [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57), [`AutomorphicForm.centralizerBorel`](def/AutomorphicForm_TwistedOrbital.html#L62), [`AutomorphicForm.localCentralizerBorel`](def/AutomorphicForm_LocalOrbitalBase.html#L197) are used.
--
--   *Characters.* `Ξ` is a finite set of homomorphisms from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$. The hypothesis `hΞc` asks each $\xi \in \Xi$ to be continuous as a $\mathbb{C}$-valued function of the idele, `hΞt` asks it to be trivial on the image of $K^\times$, and `hur` asks it to be unramified outside `SK`: for $v \notin S_K$ and a local unit $t$ at $v$ with $|t| = 1$, the value of $\xi$ at the idele which is $t$ at $v$ and $1$ elsewhere is $1$.
--
--   *Places.* `SK` and `T` are finite sets of finite places of $K$, disjoint by `hTS`.
--
--   *Local Hecke data at $T$.* `ϖKs v` lies in the valuation ring at $v$; for $v \in T$ it is irreducible (`hϖKi`) with nonzero image in the completion (`hϖKs0`). For $v \in T$, `hrKs` asserts that the family `rKs v : Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)` is a Hecke coset system for the subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) (the image of $\mathrm{GL}_2$ of the valuation ring) and the element [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68) $= \mathrm{diag}(\varpi_v, 1)$: every representative lies in the double coset, the representatives cover all left cosets contained in it, and distinct indices give distinct cosets. The element `zKs v` is, for $v \in T$, the scalar matrix $\varpi_v \cdot 1$ (`hzKs`). The functions `ks`, `js` on places record the Hecke word exponents.
--
--   *Norms and Satake parameters.* `Nw v` is, for $v \in T$, the absolute norm of the ideal of `ws v` (`hNw`), and equals $(\mathrm{absNorm}\, v)^{f_v}$ where $f_v =$ [`AutomorphicForm.SatakeCombination.slotDeg K L ws v`](def/AutomorphicForm_SatakeCombinationCoeff.html#L20) is the inertia degree of `ws v` over $v$ (`hNwf`). The functions $\zeta, s$ satisfy $\zeta_v \neq 0$ (`hζ`) and $s_v^2 = \zeta_v$ (`hs`) for $v \in T$, and `hx` requires for all $\xi \in \Xi$ and $v \in T$ that $\xi(\det \,$`heckeGen (𝓞 K) K v`$)^{f_v} = \zeta_v$, the Hecke generator at $v$ being the idelic element $\mathrm{diag}(\varpi_v, 1)$ supported at $v$.
--
--   *Test functions.* `faK` is an archimedean test factor (`hfaK`): it is $\Phi$ composed with the entry map `archEntries` for some smooth $\Phi$ on $(\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to$ mixed space$)$, and has compact support. For $v \in S_K$, `fSK v` is locally constant with compact support (`hfSK`). The family `fam` attaches to each index $m$, assigning to every $u \in T$ an element of $\mathrm{Fin}\,2 \to_0 \mathbb{N}$, a function on $\mathrm{GL}_2(\mathbb{A}_K)$. The hypothesis `hfam` requires, for every $m$ in [`AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T`](def/AutomorphicForm_SatakeCombinationCoeff.html#L32) (the set of choices, for $v \in T$, of an exponent in the support of the polynomial `slotWord K L ws v (ks v) (js v)`), the existence of a function $ff$ on $\mathrm{GL}_2$ of the finite adeles which is locally constant with compact support, which at any $h$ whose components outside $S_K \cup T$ all lie in `localIntegralSet` equals the product over $v \in S_K \cup T$ of the local factor evaluated at the $v$-component, this factor being `fSK v` for $v \in S_K$ and, for $v \in T$, the function $x \mapsto \sum_{\iota} \mathbf{1}_{\text{localIntegralSet}}\big(((\prod_i \mathrm{rKs}\,v\,(\iota\,i)) \cdot z_v^{m_v(1)})^{-1} x\big)$ with $\iota$ running over maps $\mathrm{Fin}\,(m_v(0)) \to \mathrm{Fin}\,(\mathrm{nKs}\,v)$, which vanishes at any $h$ having some component outside $S_K \cup T$ not in `localIntegralSet`, and which satisfies $\mathrm{fam}\,m\,g = \mathrm{faK}(g_\infty) \cdot ff(g_{\mathrm{fin}})$ for all $g$.
--
--   *Hyperbolic representatives.* `ΔK` is a finite set of elements of $\mathrm{GL}_2(K)$; by `hΔK` each $\gamma \in \Delta_K$ is diagonal (entries $(1,0)$ and $(0,1)$ vanish) with ratio $\gamma_{00}/\gamma_{11} \neq 1$, and by `hΔKinj` the ratio determines $\gamma$ within $\Delta_K$. The hypothesis `hΔKc` is a vanishing condition: for $m$ in the slot index, for $u \in K^\times$ with $u \neq 1$ whose value is not the ratio of any $\gamma \in \Delta_K$, and for all ideles $z$ and all $x \in \mathrm{GL}_2(\mathbb{A}_K)$, the value of $\mathrm{fam}\,m$ at $x^{-1}\,(z \cdot \mathrm{diag}(u,1))\,x$ is $0$, where $z \cdot \mathrm{diag}(u,1)$ denotes `centralScalar` of $z$ times `diagUnits2` of the idelic image of $u$ and $1$.
--
--   *Global orbital integrals.* $c_{\tau K} > 0$ is a constant and, for every $\gamma \in \mathrm{GL}_2(K)$, `τK γ` is a Haar measure (`hτK`) on the centraliser of the image `globalPoints (𝓞 K) K γ` in $\mathrm{GL}_2(\mathbb{A}_K)$; `hτKc` requires, for $\gamma \in \Delta_K$ and every $\mathbb{C}$-valued $g$, that the integral of $g$ over this centraliser equals $c_{\tau K}$ times the integral of $g(\mathrm{diag}(p_1,p_2))$ over pairs of ideles with respect to $\nu_{ZK} \times \nu_{ZK}$. The numbers `IK m γ z` are, by `hIK` (for $m$ in the slot index, $\gamma \in \Delta_K$, arbitrary $z$), orbital integrals in the sense of [`AutomorphicForm.IsOrbitalIntegralOn`](def/AutomorphicForm_TwistedOrbital.html#L248): there is a nonnegative measurable compactly supported section weight $w$ with $\int_{\text{centraliser}} w(tx)\,d\tau_K = 1$ whenever the integrand does not vanish at $x$, and $\mathrm{IK}\,m\,\gamma\,z = \int \mathrm{fam}\,m(z \cdot x^{-1}\gamma x)\,w(x)\,d(\text{adelicGLHaar})$, the central scalar $z$ multiplying the argument.
--
--   *Constants.* $\kappa_0^K$ and $\kappa^K$ are real numbers, subject to no hypothesis.
--
--   *Factorisation of the global measure.* `νA` is a measure on $\mathrm{GL}_2$ of the infinite adeles and $c_G$ a real number such that `hG` holds: for every finite set $S$ of places and every $f$, $fa$, $(fS_v)$ with $fa$ almost everywhere strongly measurable for $\nu_A$, each $fS_v$ ($v \in S$) almost everywhere strongly measurable for `localHaar`, $f(g)$ equal to $fa(g_\infty)\prod_{v \in S} fS_v(g_v)$ whenever all components of $g$ outside $S$ are integral, and $f(g) = 0$ whenever some component outside $S$ is not integral, one has $\int f \,d(\text{adelicGLHaar}) = c_G \cdot (\int fa\, d\nu_A) \cdot \prod_{v \in S} \int fS_v \,d(\text{localHaar})$.
--
--   *Factorisation of the torus measures.* For $u \in K^\times$ and an idele $z$, write $\delta(u,z) =$ `centralScalar (𝓞 K) K z * diagUnits2 (image of u) 1`. Then `τG u z` is a measure on the centraliser of $\delta(u,z)$ in $\mathrm{GL}_2(\mathbb{A}_K)$, Haar when $u \neq 1$ (`hτG`), and satisfying the same split-torus comparison with constant $c_{\tau K}$ (`hτGc`); `τA u z` is a measure on the centraliser of the archimedean part of $\delta(u,z)$, Haar when $u \neq 1$ (`hτA`); `τF u z v` is a measure on the local centraliser at $v$ of the $v$-component of the finite part of $\delta(u,z)$, Haar when $u \neq 1$ (`hτF`) and of total mass $1$ on the preimage of `localIntegralSet K v` (`hτF1`). With $c_T > 0$, the hypothesis `hT` requires, for $u \neq 1$ and any $z$, any finite $S$ and any $W$, $Wa$, $(WS_v)$ satisfying the corresponding measurability, product and vanishing conditions on the centraliser of $\delta(u,z)$, that $\int W \,d(\tau_G) = c_T \cdot (\int Wa \,d\tau_A) \cdot \prod_{v \in S} \int WS_v \,d\tau_F$.
--
--   *Idelic product datum.* `PZ` is a [`UnramifiedWhittaker.ProductMeasureData SK νZK`](def/UnramifiedWhittaker_ZetaIntegrand.html#L20), that is a positive constant `PZ.c`, a measure `PZ.νS`, a projection `PZ.projS`, an order function `PZ.ord`, together with the structure's conditions that `projS` is trivial off $S_K$ and its decomposition, Tonelli and measurability clauses for finite lists of places outside $S_K$. The hypotheses `hPo` and `hPp` identify `PZ.ord` with [`NumberField.Idele.ord K`](def/NumberField_IdeleProductMeasure.html#L13) and `PZ.projS` with [`NumberField.Idele.partAt K SK`](def/NumberField_IdeleProductMeasure.html#L90), and `hPν` states that `PZ.c` times `PZ.νS` is the pushforward under `partAt K SK` of $\nu_{ZK}$ restricted to the group [`NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K SK`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) of ideles integral, with integral inverse, outside $S_K$.
--
--   *Local and archimedean orbital integrals.* For $u \neq 1$, `IA u z` is an orbital integral of `faK` at the archimedean part of $\delta(u,z)$ with respect to $\nu_A$ and $\tau_A$ (`hIA`), and for $v \in S_K$, `IF u z v` is an orbital integral of `fSK v` at the $v$-component of the finite part of $\delta(u,z)$ with respect to `localHaar K v` and $\tau_F$ (`hIF`).
--
--   *Winding datum.* Finally $r, c \in \mathbb{N}$ and $\mathcal{A}$ is a [`AutomorphicForm.WindingDatum r T.card c`](def/AutomorphicForm_WindingDatum.html#L11), whose coefficient array is $\mathcal{A}.\mathrm{coeff}\,n = \sum_i' \lambda_i \cdot \mathrm{fibreCoeff}_i(n)$. The hypothesis `h𝒜` prescribes these coefficients: for every $n : \mathrm{Fin}\,|T| \to \mathbb{Z}$, writing $v_i =$ `T.equivFin.symm i`,
--   $$\mathcal{A}.\mathrm{coeff}\,n = \kappa_0^K \kappa^K (c_G c_T^{-1} \mathrm{PZ.c}) \sum_{u}^{\mathrm{f}} \Big(\prod_i (\sqrt{N_{w_i}}\, s_{v_i})^{-n_i}\Big) \cdot \big[\,\|\,\mathrm{partAt}_{S_K}(u-1)\,\|\,\big] \cdot \sum_{\xi \in \Xi} \int \xi(z_S)\,\big(\mathrm{IA}\,u\,z_S \cdot \prod_{v \in S_K} \mathrm{IF}\,u\,z_S\,v\big)\, d(\mathrm{PZ.\nu S}),$$
--   where $\sum^{\mathrm{f}}$ is the finsum over the set of $u \in K^\times$ with $u \neq 1$ such that [`NumberField.Idele.ord K v`](def/NumberField_IdeleProductMeasure.html#L13) of the principal idele of $u$ vanishes for every $v \notin S_K$ with $v \notin T$ and equals $f_{v_i} \cdot n_i$ at $v_i$ for each $i$; the bracketed factor is the idele norm [`NumberField.TateGlobal.ideleNorm K`](def/NumberField_TateGlobalZeta.html#L19) of `partAt K SK` applied to the principal idele of $u - 1$ when $u - 1 \neq 0$, and is $0$ otherwise.
--
--   Under these hypotheses the conclusion is the identity
--   $$\sum_{\xi \in \Xi} \;\sum_{m \in \mathrm{slotIndex}} \mathrm{slotFamilyCoeff}(m) \sum_{\gamma \in \Delta_K} \kappa_0^K \Big(\kappa^K \int \xi(z)\, \mathrm{IK}\,m\,\gamma\,z \; d\nu_{ZK}\Big) \;=\; \sum_{n} \Big(\prod_i (\sqrt{N_{w_i}}\,s_{v_i})^{k_{v_i}} \zeta_{v_i}^{\,j_{v_i}}\, \big[(X + X^{-1})^{k_{v_i}}\big]_{n_i}\Big)\, \mathcal{A}.\mathrm{coeff}\,n,$$
--   in which `slotFamilyCoeff K L ws ks js T m` is the product over $v \in T$ of $\mathrm{coeff}_{m_v}(\mathrm{slotWord}\,v\,(k_v)\,(j_v)) \cdot (\mathrm{absNorm}\,v)^{m_v(1)} / (\mathrm{absNorm}(\mathrm{ws}\,v))^{j_v}$; on the right, $n$ runs over `Fintype.piFinset` of the integer intervals $[-k_{v_i}, k_{v_i}]$, $\sqrt{\cdot}$ is the real square root of $N_{w_i}$ viewed in $\mathbb{C}$, and $[(X+X^{-1})^{k}]_{m}$ denotes the coefficient at $m$ of the Laurent polynomial $(\mathrm{T}\,1 + \mathrm{T}\,(-1))^{k}$ over $\mathbb{C}$. The sum over $\Delta_K$ carries no stabiliser weights or signs.
--
--   This is the base-field side of the hyperbolic comparison in a trace-formula argument for $\mathrm{GL}_2$: the class sums, over one representative per hyperbolic conjugacy ratio, of the adelic orbital integrals of the Hecke-word test family are rewritten as the pairing of the Satake Laurent coefficients of $(X+X^{-1})^{k_v}$ with the coefficient array of a winding datum. It is used by [`AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_classIntegral_eq_sum_satakeLaurent_mul_coeff`](thm.html#AutomorphicForm.exists_windingDatum_forall_heckeWord_mul_sum_slotFamilyCoeff_mul_sum_classIntegral_eq_sum_satakeLaurent_mul_coeff), which produces such a winding datum once and for all for every Hecke word.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted
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
    (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hfam : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
      ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
        AutomorphicForm.IsFinTestFactor K ff ∧
        (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
          (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ AutomorphicForm.localIntegralSet K v) →
            ff h = ∏ v ∈ SK ∪ T,
              (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                  ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                    (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                      (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
        (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
          (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ AutomorphicForm.localIntegralSet K v) →
            ff h = 0) ∧
        ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))

    (ΔK : Finset (GL (Fin 2) K))
    (hΔK : ∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (hΔKinj : ∀ γ ∈ ΔK, ∀ γ' ∈ ΔK,
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 =
        (γ' : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ' : Matrix (Fin 2) (Fin 2) K) 1 1 → γ = γ')
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τK : ∀ γ : GL (Fin 2) K,
      Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτK : ∀ γ : GL (Fin 2) K, (τK γ).IsHaarMeasure)
    (hτKc : ∀ γ ∈ ΔK, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τK γ) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (IK : (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ))) → GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ γ ∈ ΔK,
      ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g))
          (IK m γ z))

    (hΔKc : ∀ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T, ∀ u : Kˣ, (u : K) ≠ 1 →
      (∀ γ ∈ ΔK, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ (u : K)) →
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          fam m (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) = 0)
    (κ₀K κK : ℝ)

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

    (PZ : UnramifiedWhittaker.ProductMeasureData SK νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K SK)
    (hPν : ENNReal.ofReal PZ.c • PZ.νS =
      Measure.map (NumberField.Idele.partAt K SK)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))

    (r c : ℕ) (𝒜 : AutomorphicForm.WindingDatum r T.card c)
    (h𝒜 : ∀ n : Fin T.card → ℤ, 𝒜.coeff n =
      ((κ₀K : ℂ) * ((κK : ℝ) : ℂ) * ((cG * cT⁻¹ * PZ.c : ℝ) : ℂ)) *
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
              (IA u zS * ∏ v ∈ SK, IF u zS v) ∂PZ.νS) :
    ∑ ξ ∈ Ξ, ∑ m ∈ AutomorphicForm.SatakeCombination.slotIndex K L ws ks js T,
        AutomorphicForm.SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∑ γ ∈ ΔK, (κ₀K : ℂ) *
            (((κK : ℝ) : ℂ) *
              ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK m γ z ∂νZK) =
      ∑ n ∈ Fintype.piFinset (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
        (∏ i : Fin T.card,
            ((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 * ζ (T.equivFin.symm i).1 ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) *
          𝒜.coeff n := by sorry
