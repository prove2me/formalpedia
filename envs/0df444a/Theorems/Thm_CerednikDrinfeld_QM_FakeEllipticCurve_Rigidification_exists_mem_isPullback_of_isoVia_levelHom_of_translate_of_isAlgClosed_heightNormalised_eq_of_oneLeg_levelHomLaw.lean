-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_mem_isPullback_of_isoVia_levelHom_of_translate_of_isAlgClosed_heightNormalised_eq_of_oneLeg_levelHomLaw
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_mem_isPullback_of_isoVia_levelHom_of_translate_of_isAlgClosed_heightNormalised_eq_of_oneLeg_levelHomLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/fb5a3bdd-1225-5de6-8d93-a9b099456779
-- title:
--   Isomorphisms of rigidified curves over one leg come from Γ
-- statement:
--   Arithmetic data. Two distinct primes $r$ and $\bar r$ and a level $N\neq 0$ are fixed, with $\bar r\neq r$, $r\nmid N$, $\bar r\nmid N$ and $N$ squarefree (`hrr`, `hrN`, `hrbarN`, `hN`).
--
--   Base rings. $\mathcal O$ is a characteristic-zero discrete valuation domain (`hdvr`) with an irreducible element $\pi$ (`hπ`), $\pi$-adically complete (`hcomplete`), whose residue ring has exactly $r$ elements (`hres`) and satisfies $(r)=(\pi)$ (`hunr`, absolute unramifiedness); $K_0$ is a characteristic-zero fraction field of $\mathcal O$. Further, $\mathrm{Onr}$ is a characteristic-zero $\mathcal O$-algebra domain equipped with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, $\pi$-adically complete (`hOnr_complete`), with $(\pi)$ maximal (`hOnr_max`), every element integral over $\mathcal O$ modulo $\pi$ (`hOnr_alg`), every monic polynomial of positive degree having a root modulo $\pi$ (`hOnr_closed`), and $\mathrm{Fr}(x)\equiv x^{r}\pmod\pi$ (`hFr`): thus the completion of a maximal unramified extension with its Frobenius. Finally $v\!\det:\mathrm{GL}_2(K_0)\to\mathbb Z$ (written multiplicatively) is a homomorphism computing the $\pi$-valuation of the determinant up to units of $\mathcal O$ (`hvdet`).
--
--   Indefinite side and moduli. $a,b\in\mathbb Q$ are such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and is a division algebra locally exactly at the primes over $r$ and $\bar r$ (`hB`), $\Lambda$ is a maximal order in it (`hΛ`), and $\mathcal X\to\operatorname{Spec}\mathcal O$ with its point assignment `pt` is a coarse moduli space for fake elliptic curves of level $N$ over $\Lambda$ (`h𝒳`: isomorphism invariance, compatibility with base change, surjectivity and injectivity on geometric points, and the universal property). An auxiliary level $n\geq 3$ is fixed with $r\nmid n$, $\bar r\nmid n$ and $\gcd(n,N)=1$, together with a fine moduli space $M\to\operatorname{Spec}\mathcal O$ with point assignment `ptF` for curves with full level-$n$ structure (`hM`), and a group $G$ acting on $M$ through $\rho$ with labels $\chi:G\to\Lambda$ realising twists of the level-$n$ structure (`hρ`: the action is over the base, implements `IsTwist` on points, and $\chi$ is a bijection onto the invertible classes modulo $n$). A morphism $p:M\to\mathcal X$ over the base is given, invariant under $\rho$ and compatible with `ptF` and `pt` (`hp`, `hρp`, `hp_pt`).
--
--   Hecke and Atkin–Lehner data. For every prime $\ell\notin\{r,\bar r\}$ a coarse moduli space $\mathcal Y_\ell\to\operatorname{Spec}\mathcal O$ for curves with extra level structure at $\ell$ is given (`h𝒴`), with two degeneracy maps $d_0,d_1:\mathcal Y_\ell\to\mathcal X$ over the base (`hd₀f`, `hd₁f`) inducing on points the forgetful map and the $\ell$-isogeny quotient (`hd₀`, `hd₁`); two endomorphisms $a_r$, $a_{\bar r}$ of $\mathcal X$ over the base (`harf`, `harbarf`) induce the Atkin–Lehner quotients at $r$ and $\bar r$ (`har`, `harbar`).
--
--   Definite side. $a_1,b_1\in\mathbb Q$ are such that $\mathbb H[\mathbb Q,a_1,b_1]$ is definite and ramified exactly at $\bar r$ (`hdef`), with a maximal order $\Lambda_1$, an Eichler order $R_1$ of level $N$ contained in $\Lambda_1$ (`hΛ₁`, `hR₁`, `hRΛ₁`), a finite-adelic unit $n_1$ in the prime Hecke set of $R_1$ at $r$ such that $R_1\cap n_1R_1n_1^{-1}$ is Eichler of level $Nr$ (`hn₁`, `hS₁`), an injective $\mathbb Q$-algebra embedding $\iota_0$ into $M_2(K_0)$ (`hι₀`), and a place $v$ above $r$ (`hv`). The group $\Gamma_{\mathrm t}$ is the group of units integral away from $v$, $\Gamma_{\mathrm t}=\mathrm{awayUnits}\,R_1\,v$ (`hΓt`); for each prime $\ell\notin\{r,\bar r\}$ elements $s_\ell$ and adelic elements $sf_\ell$ are given whose local components agree with $s_\ell$ away from $r$, are trivial at $r$, whose product with the diagonal $\ell$ lies in the appropriate Hecke set of $R_1\cap n_1R_1n_1^{-1}$, and with $\mathrm{nrd}(s_\ell)=\ell$ (`hs`, four clauses), together with $\Gamma_{\mathrm t,\ell}=\Gamma_{\mathrm t}\cap s_\ell\Gamma_{\mathrm t}s_\ell^{-1}$ (`hΓtℓ`) and an element $\bar w$ of reduced norm $\bar r$ normalising $\Gamma_{\mathrm t}$ (`hwbar`).
--
--   Base curve, formal module and dictionary. All rational integers lie in $\Lambda$ (`hΛℤ`), and `coord` is an order coordinate system for $\Lambda$ at $r$ (`hcoord`). Over the residue ring $\mathrm{Onr}/(\pi)$ there are: a fake elliptic curve $A_0$, a formal $\mathcal O_D$-module $X_0$ of height $4$ (`hX₀`), two-dimensional formal coordinates $\theta_0$ on $A_0$ identifying its formal group with $X_0$ through `coord` (`hA₀`), and families $e_\gamma,e'_\gamma$ of endomorphisms of $A_0$ over the base indexed by $\Gamma_{\mathrm t}$ with degrees $\deg\gamma$ (`he`). The hypotheses `hE1`, `hE1mul`, `hE1sc`, `hE1'`, `hE2`, `hE3`, `hE4` (summarised here) assert: each $(e_\gamma,e'_\gamma)$ is an isogeny pair of degree $r^{\deg\gamma}$ preserving the $N$-level structure; $e$ is multiplicative up to multiplication by powers of $r$; central integers $\gamma$ give multiplication maps up to $r$-powers, and conversely only scalars do; every injective matrix realisation of the centraliser of the $X_0$-action admits $g\in\mathrm{GL}_2(K_0)$ for which $e_\gamma$ is induced on formal coordinates by an element $\varepsilon$ with $E_0\varepsilon=r^{k_\gamma}g\,\iota_0(\gamma)\,g^{-1}$; the action of $\Gamma_{\mathrm t}$ on a full level-$n$ structure is given by labels in $\Lambda$, multiplicative and compatible with scalars modulo $n$; and every $r$-power isogeny, level-preserving, of a curve pulled back from $A_0$ over an algebraically closed field is induced by some $e_\gamma$ up to $r$-powers. An order $R_2\subseteq R_1$ with $r$-power denominators relative to $R_1$ and a family $\hat e$ of endomorphisms of $A_0$ indexed by $R_2$ are given (`hR₂`, `hR₂o`, `hR₂r`, `hê`), subject to `hE5a`, `hE5b1`, `hE5b2`, `hE5b3`, `hE5c`, `hE5d`, `hE5e` (summarised here): $\hat e$ is additive on points, commutes with the $\Lambda$-action and preserves the level; it is unital, multiplicative, sends integers to multiplications, sends $x\,\mathrm{star}(x)$ to multiplication by $\mathrm{nrd}(x)$, agrees with $e$ on $\Gamma_{\mathrm t}$ up to $r$-powers, and both families admit a common matrix realisation conjugate to $\iota_0$.
--
--   Special formal moduli and the Drinfeld comparison. A ring map $\iota$ from the Witt ring $\mathbb Z_{r^2}$ to $\mathrm{Onr}$ is fixed, together with a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $\mathrm{Onr}/(r)$ (`hΦ`, `hΦ4`), a moduli package $MD$ over $\mathrm{Onr}$ which is a Zariski sheaf (`hMD`), and a map $\eta$ from rigidified objects to $MD$-points whose law `hη` (three clauses) says that admissible rigidified objects have equal images precisely when isomorphic, that $\eta$ is natural in the base, and that every $MD$-point is, locally on a distinguished open cover, the image of an admissible rigidified object; $E_0$ is an injective ring map from the centraliser of the $\Phi$-action and $\varpi$ to $M_2(K_0)$ whose image is commensurable with $M_2(\mathcal O)$ (`hE₀`). The data $eD$, with `hnatD`, `hbijD`, `hfstD`, `hGLD`, `hPiD`, `hPiexD`, constitute a natural bijection between the functor of $MD$-points with a leg and the product of the functor of $\mathrm{Onr}$-algebra maps with the Deligne functor $\Omega$, preserving the leg component, matching the $\mathrm{GL}_2(K_0)$-action on the moduli side with the twisted action on $\Omega$, matching $\pi$-translation with the Frobenius twist of the leg, and with $\pi$-translates always existing. A map $\kappa$ from $\mathrm{Onr}/(\pi)$ to $\mathrm{Onr}/(r)$ compatible with the quotient maps (`hκ`) and an isogeny $\beta_0$ from $\Phi$ to $X_0$ base changed along $\kappa$, of height $4n_0$ (`hβ₀`), are fixed, as is a full level-$n$ structure $P_0$ on $A_0$.
--
--   The $\bar r$-Atkin–Lehner datum at the base. A second curve $A_{0w}$ over $\mathrm{Onr}/(\pi)$ with maps $aw,aw'$ realising the Atkin–Lehner quotient at $\bar r$ (`hALw`) and maps $bw,bw'$ forming an isogeny pair of degree $r^{kw}$ preserving the level (`hBSw`, `hBSwlev`) is given, and `hJOINTw` asserts that for every injective matrix realisation there is one $g$ simultaneously conjugating $\iota_0$ into the realisations of all $e_\gamma$ and of $aw\circ bw$, the latter corresponding to $\bar w$, each up to a power of $r$.
--
--   The comparison functor $\Xi$. A map $\Xi$ sending a rigidified curve over a $\pi$-nilpotent Noetherian $\mathcal O$-algebra $B$ with leg $\psi$ to a $G$-point of $MD$ is given, subject to: `hΞleg` (over connected $B$ the leg of $\Xi$ is a Frobenius twist of $\psi$), `hΞnat` (compatibility with pullbacks of rigidified curves), `hΞiso` (invariance under isomorphisms of rigidified curves matched up to $r$-power comparison data), and `hΞdef` (for a curve with a formal module structure there are $j\le 1$ and an admissible rigidified object $t$ transporting the rigidification, with $\Xi$ equal to $\eta$ of $t$ over the $(-j)$-Frobenius twist of $\psi$).
--
--   The element $g_0\in\mathrm{GL}_2(K_0)$ is fixed, and the following hypotheses are imposed, all for Noetherian $\pi$-nilpotent $\mathcal O$-algebras and, where stated, connected ones: `heqΓ` and `heqW` (translating a rigidification by $e_\gamma$, respectively by $aw\circ bw$ in the presence of an Atkin–Lehner quotient at $\bar r$, moves $\Xi$ by the action of $r^{c}\,g_0\iota_0(\gamma)g_0^{-1}$, respectively $r^{c}\,g_0\iota_0(\bar w)g_0^{-1}$, for some $c\in\mathbb Z$); `hK1`–`hK4` (every pair consisting of a leg and a Deligne datum is, via the $g_0^{-1}$-twisted action, the image of a rigidified curve whose $\Xi$-leg is the twisted leg; two such are isomorphic, compatibly with the rigidifications up to $r$-powers; such data propagate along base change; and they lift along surjections with square-zero-like kernel); `hC0e`, `hC0u` (existence and uniqueness of the norm-level transport of $P_0$ along a rigidification); $\Theta f$ with `hnat`, `hG`, `hC2`, `hC2c` (a natural family of nilpotent-level points of $M$ indexed by a leg, a Deligne datum and an element of $G$, equivariant for $\rho$, which at $1\in G$ agrees with `ptF` applied to the curve with its transported level-$n$ structure and, after composition with $p$, with `pt` applied to the curve); `hEX`, `hβ₀'`, `hβ₀'β₀`, `hβ₀β₀'`, `hEXE₀` (a quasi-inverse isogeny $\beta_0'$ to $\beta_0$ with composites the multiplications by $r^{N\beta}$, and the comparison $E_0\circ(\text{transport})=r^{N\beta}EX$ of the two matrix realisations); $gX$, $\varepsilon_\gamma$, $k_\gamma$ with `hεk` (one fixed choice of the realisation of $e_\gamma$ as $r^{k_\gamma}gX\,\iota_0(\gamma)\,gX^{-1}$).
--
--   The level homomorphism. A homomorphism $\mathrm{slack}:\Gamma_{\mathrm t}\to(\mathbb Z/n)^\times$ with $\mathrm{slack}(\gamma)\,r^{(-k_\gamma)^+}=r^{k_\gamma^+}$ in $\mathbb Z/n$ (`hslack`) and a homomorphism $\theta_{\mathrm t}:\Gamma_{\mathrm t}\to G$ such that, on the base level structure $P_0$, translating $e_\gamma(P_0)$ by $\chi(\theta_{\mathrm t}\gamma)$ gives the multiple of $P_0$ by the representative of $\mathrm{slack}(\gamma)$ (`hθt`) are fixed.
--
--   The translation clause. `hC3` asserts: for a connected Noetherian $\pi$-nilpotent $B$, a leg $\psi$, a Deligne datum $P$, a curve $E$ over $B$ and a rigidification $\varrho$ relative to the $(-v\!\det g_0)$-twist of $\psi$ whose $\Xi$-leg is that twist and whose image under the $g_0^{-1}$-twisted action is $(\psi,P)$, and for $\gamma\in\Gamma_{\mathrm t}$ and $(\psi',P')$ obtained from $(\psi,P)$ by the twisted action of $\iota_0(\gamma)$, there is a rigidification $\varrho'$ of the same $E$ over $\psi'$ with the same two normalisation properties, whose norm-level transport of $P_0$ differs from that of $\varrho$ by the translation by $\chi(\theta_{\mathrm t}\gamma)$, and such that, for every prime $\ell\neq r$ invertible in $B$ and every extra level structure at $\ell$ on $A_0$ stable under $e_\gamma$, two extra level structures on $E$ compatible with it through $\varrho$ and through $\varrho'$ respectively cut out the same points of $E$.
--
--   Conclusion. Let $k$ be an algebraically closed field which is an $\mathcal O$-algebra with $\pi$ nilpotent in $k$, let $\psi:\mathrm{Onr}\to k$ be an $\mathcal O$-algebra map, let $P,P'$ be Deligne data over $k$, and let $E,E'$ be fake elliptic curves of level $N$ over $\Lambda$ with rigidifications $\varrho$ on $E$ and $\varrho'$ on $E'$, both relative to the leg $\psi_0:=\mathrm{Fr}^{-v\!\det g_0}\!\circ\psi$. Assume that the leg of $\Xi(E,\varrho)$ is $\psi_0$ and that the $g_0^{-1}$-twisted action carries $eD(\Xi(E,\varrho))$ to $(\psi,P)$, and likewise that the leg of $\Xi(E',\varrho')$ is $\psi_0$ and that the $g_0^{-1}$-twisted action carries $eD(\Xi(E',\varrho'))$ to $(\psi,P')$. Assume further that $i:E.A\cong E'.A$ is an isomorphism over $k$ compatible with the group laws, the $\Lambda$-actions and the $N$-level subschemes. Then there exists a unit $\gamma$ of $\mathbb H[\mathbb Q,a_1,b_1]$ lying in $\Gamma_{\mathrm t}$ such that the following three assertions hold.
--
--   First, $(\psi,P')$ is obtained from $(\psi,P)$ by the twisted action of $\iota_0(\gamma)$: the leg satisfies $\psi=\mathrm{Fr}^{-v\!\det\iota_0(\gamma)}\!\circ\psi$, and $P'$ is the pullback of $P$ along $\iota_0(\gamma)^{-1}$ in the sense of Deligne data.
--
--   Second, for every full level-$n$ structure $P_n$ on $E$ and every full level-$n$ structure $P_n'$ on $E'$ which are norm-level transports of $P_0$ along $\varrho$ and along $\varrho'$ respectively, the image under $i$ of the translate of $P_n$ by the action of $\chi(\theta_{\mathrm t}\gamma)$ on $E$ equals $P_n'$.
--
--   Third, for every prime $\ell\neq r$ invertible in $k$, every extra level structure $\mathcal K$ at $\ell$ on $A_0$ (named `K₀` in the statement, distinct from the fraction field), and all extra level structures $C$ on $E$ and $C'$ on $E'$ at $\ell$ such that points of $\varrho.Eb$ over the base $k/(\pi)$ lying in $C$ have their images under $\varrho.\varphi$ followed by $\varrho.gA$ lying in $\mathcal K$, and similarly for $C'$ with $\varrho'$, the following two conditions are equivalent: $i$ identifies $C$ with $C'$, that is, for every scheme $T$ over $\operatorname{Spec} k$ and every point $R$ of $E$ over $T$, $R$ factors through $C$ if and only if $R$ followed by $i$ factors through $C'$; and $e_\gamma$ stabilises $\mathcal K$, that is, every point of $A_0$ over any base which factors through $\mathcal K$ has its $e_\gamma$-image factoring through $\mathcal K$.
--
--   This is the curve-level comparison step of the Čerednik–Drinfeld uniformisation as organised in this formalisation: over a single leg $\psi$ of the unramified base, an isomorphism between two rigidified fake elliptic curves with the same leg is shown to be induced by an element of the arithmetic group $\Gamma_{\mathrm t}$ of the definite quaternion algebra, together with the effect of that element on the auxiliary level-$n$ structure (through the level homomorphism $\theta_{\mathrm t}$) and on the extra level structures away from $r$. It is used in the construction of the fine family on the $p$-adic uniformisation side, being cited by [`CerednikDrinfeld.QM.IsFineModuli.exists_levelHom_translate_fibre_of_fineFamily_of_isNoetherianRing_heightNormalised_conn_eq_oneLegC5`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_levelHom_translate_fibre_of_fineFamily_of_isNoetherianRing_heightNormalised_conn_eq_oneLegC5).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_mem_isPullback_of_isoVia_levelHom_of_translate_of_isAlgClosed_heightNormalised_eq_of_oneLeg_levelHomLaw.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_mem_isPullback_of_isoVia_levelHom_of_translate_of_isAlgClosed_heightNormalised_eq_of_oneLeg_levelHomLaw

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (p : M ⟶ 𝒳) (hp : p ≫ f = fM) (hρp : ∀ h : G, (ρ h).hom ≫ p = p)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (d₀ d₁ : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ 𝒳) (hd₀f : ∀ ℓ, d₀ ℓ ≫ f = g ℓ) (hd₁f : ∀ ℓ, d₁ ℓ ≫ f = g ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 ≫ d₀ ℓ = (pt S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT ℓ S s u).1 ≫ d₁ ℓ = (pt S s d).1)

    (ar arbar : 𝒳 ⟶ 𝒳) (harf : ar ≫ f = f) (harbarf : arbar ≫ f = f)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt S s E).1 ≫ ar = (pt S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient rbar E E' → (pt S s E).1 ≫ arbar = (pt S s E').1)

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (s : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ ℓ : HeckeTower.AwayPrime r rbar,
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γtℓ : HeckeTower.AwayPrime r rbar → Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓtℓ : ∀ ℓ : HeckeTower.AwayPrime r rbar, Γtℓ ℓ = Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom)

    (wbar : (ℍ[ℚ, a₁, b₁])ˣ) (hwbar : nrd (wbar : ℍ[ℚ, a₁, b₁]) = ((rbar : ℕ) : ℚ) ∧ ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt → wbar * x * wbar⁻¹ ∈ Γt)

    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (e e' : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f) (deg : ↥Γt → ℕ)

    (hX₀ : X₀.HasHeight 4) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (hE1 :
      (∀ γ : ↥Γt, FakeEllipticCurve.IsIsogenyPair (r ^ deg γ) A₀ A₀ (e γ) (e' γ) ∧ FakeEllipticCurve.PreservesLevel A₀ A₀ (e γ) (he γ)))
    (hE1mul :
      (∀ γ γ' : ↥Γt, ∃ i j : ℕ,
          e (γ * γ') ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ' ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩))
    (hE1sc :
      (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
          ∃ i : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c * ((r ^ i : ℕ) : ℤ) : ℤ) : ℚ), hΛℤ _⟩))

    (hE1' :
      (∀ (γ : ↥Γt), (∃ (i c : ℕ), 0 < c ∧ e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c : ℤ) : ℚ), hΛℤ _⟩) →
          ∃ c : ℚ, ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])))

    (hE2 :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, ∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (hE3 :
      (∀ P₀ : A₀.FullLevel n, ∃ lab : ↥Γt → ↥Λ,
        (∀ γ : ↥Γt, mapPt (e γ) (he γ) P₀.P = pushPt (A₀.act (lab γ)) (A₀.act_over (lab γ)) P₀.P) ∧
        (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
        (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
            ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b]))))

    (hE4 :
      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k]
          (A : FakeEllipticCurve Λ N k) (gA : A.A ⟶ A₀.A),
          FakeEllipticCurve.IsPullbackVia (algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k) A₀ A gA →
          (∀ (φ ψ : A.A ⟶ A.A) (d : ℕ) (hφ : φ ≫ A.f = A.f),
              FakeEllipticCurve.IsIsogenyPair (r ^ d) A A φ ψ → FakeEllipticCurve.PreservesLevel A A φ hφ →
              ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ A.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ gA = gA ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)))

    (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁) (hR₂o : IsOrder R₂)
          (hR₂r : ∀ x : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (x : ℍ[ℚ, a₁, b₁]) ∈ R₂)
          (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ x, ê x ≫ A₀.f = A₀.f)

        (hE5a : ∀ x : ↥R₂,
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
              mapPt (ê x) (hê x) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê x) (hê x) P) (mapPt (ê x) (hê x) Q)) ∧
          (∀ m : ↥Λ, A₀.act m ≫ ê x = ê x ≫ A₀.act m) ∧
          FakeEllipticCurve.PreservesLevel A₀ A₀ (ê x) (hê x))

        (hE5b1 : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A)
        (hE5b2 : ∀ (x y : ↥R₂) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
            ê ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê x)
        (hE5b3 : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)

        (hE5c : ∀ (x y : ↥R₂) (nx : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (x : ℍ[ℚ, a₁, b₁]) → nrd (x : ℍ[ℚ, a₁, b₁]) = (nx : ℚ) →
            ê y ≫ ê x = A₀.act ⟨((nx : ℤ) : ℚ), hΛℤ nx⟩)

        (hE5d : ∀ (γ : ↥Γt) (x : ↥R₂) (k : ℕ),
            (x : ℍ[ℚ, a₁, b₁]) = ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) →
            ∃ i j : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê x ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

        (hE5e : ∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
          ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
            (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                  J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                  θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                    mapPt (e γ) (he γ) (θ₀ B' s)) ∧
              E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧
            (∀ x : ↥R₂, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kx : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                  J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                  θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                    mapPt (ê x) (hê x) (θ₀ B' s)) ∧
              E₀ ε = ((r : K₀) ^ kx) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (x : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (MD : ModuliPackage.{0, 0} r Onr) (hMD : MD.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → MD.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = MD.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : MD.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  MD.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

      (eD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 MD).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)

      (hnatD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 MD).obj B), eD B' hB' ((ModuliPackage.G 𝒪 MD).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (eD B hB x))

      (hbijD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (eD B hB))

      (hfstD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 MD).obj B), (eD B hB x).1 = x.ψ)

      (hGLD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (eD B hB x) (eD B hB x'))

      (hPiD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → eD B hB x' = (frobTwist Onr Fr 1 (eD B hB x).1, (eD B hB x).2))

      (hPiexD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 MD).obj B), ∃ x' : (ModuliPackage.G 𝒪 MD).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x')

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (P₀ : A₀.FullLevel n)

    (A₀w : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f)
    (kw : ℕ) (bw : A₀w.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀w.f) (bw' : A₀.A ⟶ A₀w.A) (habw : (aw ≫ bw) ≫ A₀.f = A₀.f)
    (hALw : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw')
    (hBSw : FakeEllipticCurve.IsIsogenyPair (r ^ kw) A₀w A₀ bw bw') (hBSwlev : FakeEllipticCurve.PreservesLevel A₀w A₀ bw hbw)
    (hJOINTw :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
          (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧

          (∃ (εw : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (k_w : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ v : Fin 2 → B', (∀ i, v i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εw : MvFormalGroup.End X₀.F).toPowerSeries i) v) =
                  mapPt (aw ≫ bw) habw (θ₀ B' v)) ∧
              E₀ εw = ((r : K₀) ^ k_w) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((wbar : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))))

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 MD B)

    (hΞleg :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ), ∃ k : ℤ, (Ξ B ψ hB x).ψ = frobTwist Onr Fr k ψ))

    (hΞnat :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
          (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g),
          FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2 → Ξ B' (φ.comp ψ) hB' x' = (Ξ B ψ hB x).map φ))

    (hΞiso :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
          FakeEllipticCurve.IsoVia x.1 x'.1 i hi →
          (∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
            (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
            (i₁ j₁ : ℕ),
            ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            Ξ B ψ hB x = Ξ B ψ hB x'))

    (hΞdef :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩))

    (g₀ : Matrix.GeneralLinearGroup (Fin 2) K₀)

      (heqΓ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (E : FakeEllipticCurve Λ N B) (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E) (γ : ↥Γt),
          FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ (e γ) ρ ρ' →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) (γ : (ℍ[ℚ, a₁, b₁])ˣ) * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨E, ρ'⟩))

      (heqW : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hrbarB : IsUnit ((rbar : ℕ) : B))
          (E Ef : FakeEllipticCurve Λ N B)
          (q : E.A ⟶ Ef.A) (hq : q ≫ Ef.f = E.f) (q' : Ef.A ⟶ E.A) (hq' : q' ≫ E.f = Ef.f),
          FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar E Ef q hq q' hq' →
          ∀ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef),
          (∃ (qb : ρ.Eb.A ⟶ ρf.Eb.A) (_ : qb ≫ ρf.gb = ρ.gb ≫ q) (_ : qb ≫ ρf.Eb.f = ρ.Eb.f)
            (uA : ρf.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (_ : uA ≫ ρ.gA = ρf.gA)
            (ewb : ρ.Ab.A ⟶ ρ.Ab.A) (_ : ewb ≫ ρ.gA = ρ.gA ≫ (aw ≫ bw)) (_ : ewb ≫ ρ.Ab.f = ρ.Ab.f)
            (i j : ℕ),
            qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ewb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) wbar * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨Ef, ρf⟩))

      (hK1 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
          ∃ (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
            (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) ∧
            OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P))

      (hK2 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (E' : FakeEllipticCurve Λ N B) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E'),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E', ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E', ϱ'⟩)) (ψ, P) →
            ∃ (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f), FakeEllipticCurve.IsoVia E E' i hi ∧
              (∃ (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
                (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
                (i₁ j₁ : ℕ),
                ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

      (hK3 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
          (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
            ∃ (E' : FakeEllipticCurve Λ N B') (g : E'.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E E' g)
              (ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) E'),
              FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ϱ ϱ' ∧
              (Ξ B' (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) hB' ⟨E', ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) ∧ OmegaNr.IsTwistedAct π Onr Fr vdet B' g₀⁻¹ (eD B' hB' (Ξ B' (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) hB' ⟨E', ϱ'⟩)) ((φ.comp ψ), ((Omega K₀ π).map φ P)))

      (hK4 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [IsNoetherianRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
            (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g) (ϱ₀ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) E₀),
            (Ξ B₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) hB₀ ⟨E₀, ϱ₀⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) →
            ∃ (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (ϱ₀' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) E₀),
              FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ϱ ϱ₀' ∧ (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) ∧
              ∀ P₀' : (Omega K₀ π).obj B₀,
                OmegaNr.IsTwistedAct π Onr Fr vdet B₀ g₀⁻¹ (eD B₀ hB₀ (Ξ B₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) hB₀ ⟨E₀, ϱ₀⟩)) ((p.comp ψ), P₀') ↔
                  OmegaNr.IsTwistedAct π Onr Fr vdet B₀ g₀⁻¹ (eD B₀ hB₀ (Ξ B₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) hB₀ ⟨E₀, ϱ₀'⟩)) ((p.comp ψ), P₀'))

      (hC0e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E)
          (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2), E.IsFormalModuleVia coord X θ →
          ∃ Pn : E.FullLevel n, FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn)

      (hC0u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (Pn Pn' : E.FullLevel n),
          FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn' → Pn.P = Pn'.P)

      (Θf : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)

      (hnat : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))

      (hG : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g h : G),
          (Scheme.nilpPoints.mapHom fM fM (ρ h).hom (hρ.over_base h)).app B (Θf B hB (x, g * h)) = Θf B hB (x, g))

      (hC2 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (Pn : E.FullLevel n),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn →
            (Θf B hB ((ψ, P), (1 : G))).1 = (ptF B (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))) ⟨E, Pn⟩).1)

    (hC2c : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
            (Θf B hB ((ψ, P), (1 : G))).1 ≫ p = (pt B (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))) E).1)

    (EX : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀) (hEX : Function.Injective EX)
    (Nβ : ℕ) (β₀' : Series (Onr ⧸ pIdeal r Onr))
    (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
    (hβ₀'β₀ : β₀'.comp β₀ = Φ.act ((r : Zp2 r) ^ Nβ)) (hβ₀β₀' : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ Nβ))
    (hEXE₀ : ∀ εX : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
        ∃ eΦ : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})),
          (eΦ : MvFormalGroup.End Φ.F).toPowerSeries =
            β₀'.comp ((Series.map κ (εX : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
          E₀ eΦ = ((r : K₀) ^ Nβ) • EX εX)

    (gX : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (εγ : ↥Γt → ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ↥Γt → ℤ)
    (hεk : ∀ γ : ↥Γt,
      (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
          J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m (((εγ γ) : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
            mapPt (e γ) (he γ) (θ₀ B' s)) ∧
      EX (εγ γ) = ((r : K₀) ^ kγ γ) • ((gX : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
        ((gX⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))

    (slack : ↥Γt →* (ZMod n)ˣ)
    (hslack : ∀ γ : ↥Γt, ((slack γ : (ZMod n)ˣ) : ZMod n) * (r : ZMod n) ^ (-(kγ γ)).toNat = (r : ZMod n) ^ (kγ γ).toNat)
    (θt : ↥Γt →* G)
    (hθt : ∀ γ : ↥Γt, pushPt (A₀.act (χ (θt γ))) (A₀.act_over (χ (θt γ))) (mapPt (e γ) (he γ) P₀.P) =
        pushPt (A₀.act ⟨((((slack γ : (ZMod n)ˣ) : ZMod n).val : ℤ) : ℚ), hΛℤ _⟩) (A₀.act_over _) P₀.P)

    (hC3 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
          ∀ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt) (ψ' : Onr →ₐ[𝒪] B) (P' : (Omega K₀ π).obj B),
            OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) (ψ, P) (ψ', P') →
            ∃ ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') E,
              (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') hB ⟨E, ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') ∧ OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') hB ⟨E, ϱ'⟩)) (ψ', P') ∧
              (∀ (Pn Pn' : E.FullLevel n), FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ' Pn' →
                  Pn'.P = pushPt (E.act (χ (θt ⟨γ, hγ⟩))) (E.act_over (χ (θt ⟨γ, hγ⟩))) Pn.P) ∧
              (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ r → IsUnit ((ℓ : ℕ) : B) → ∀ (K₀ : A₀.ExtraLevel ℓ),
                  (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (R : SchemeHomOver t A₀.f),
                      FactorsThrough K₀.levK R → FactorsThrough K₀.levK (mapPt (e ⟨γ, hγ⟩) (he ⟨γ, hγ⟩) R)) →
                  ∀ (C C' : E.ExtraLevel ℓ), (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
                  (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) → (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ'.Eb.f),
                  (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ϱ'.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ'.φ) ≫ ϱ'.gA) →
                    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (R : SchemeHomOver t E.f),
                      FactorsThrough C.levK R ↔ FactorsThrough C'.levK R))
    :

      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π))
          (ψ : Onr →ₐ[𝒪] k) (P P' : (Omega K₀ π).obj k)
          (E : FakeEllipticCurve Λ N k) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (E' : FakeEllipticCurve Λ N k) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E'),
          (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet k g₀⁻¹ (eD k hk (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ⟩)) (ψ, P) →
          (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E', ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet k g₀⁻¹ (eD k hk (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E', ϱ'⟩)) (ψ, P') →
          ∀ (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f), FakeEllipticCurve.IsoVia E E' i hi →
            ∃ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt),
              OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) (ψ, P) (ψ, P') ∧
              (∀ (Pn : E.FullLevel n) (Pn' : E'.FullLevel n), FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ' Pn' →
                  mapPt i.hom hi (pushPt (E.act (χ (θt ⟨γ, hγ⟩))) (E.act_over (χ (θt ⟨γ, hγ⟩))) Pn.P) = Pn'.P) ∧
              (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ r → IsUnit ((ℓ : ℕ) : k) → ∀ (K₀ : A₀.ExtraLevel ℓ) (C : E.ExtraLevel ℓ) (C' : E'.ExtraLevel ℓ),
                  (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) (R : SchemeHomOver t' ϱ.Eb.f),
                  (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) → (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) (R : SchemeHomOver t' ϱ'.Eb.f),
                  (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ϱ'.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ'.φ) ≫ ϱ'.gA) →
                  ((∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (R : SchemeHomOver t E.f),
                      FactorsThrough C.levK R ↔ FactorsThrough C'.levK (mapPt i.hom hi R)) ↔
                   (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (R : SchemeHomOver t A₀.f),
                      FactorsThrough K₀.levK R → FactorsThrough K₀.levK (mapPt (e ⟨γ, hγ⟩) (he ⟨γ, hγ⟩) R))))) := by sorry
