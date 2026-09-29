-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/e265c210-7c13-5142-966d-f56cf7f734af
-- title:
--   Ratio-window open and degree laws on the exponent-D stratum
-- statement:
--   The statement is made inside the full frame of the Čerednik–Drinfeld window construction; the data and hypotheses are listed group by group, with the content of the longer groups summarised but no hypothesis passed over.
--
--   **Coefficients and residue data.** Primes $r$, $\bar r$ and a nonzero natural number $N$ with $\bar r \neq r$, $r \nmid N$, $\bar r \nmid N$ and $N$ squarefree (`hrr`, `hrN`, `hrbarN`, `hN`). A characteristic-zero domain $\mathcal{O}$ which is a discrete valuation ring (`hdvr`) with an irreducible element $\pi$ (`hπ`), complete for the $\pi$-adic topology (`hcomplete`), whose residue ring $\mathcal{O}/\pi$ has exactly $r$ elements (`hres`) and in which $(r) = (\pi)$ (`hunr`), together with a characteristic-zero fraction field $K_0$ of $\mathcal{O}$. A characteristic-zero domain $Onr$ over $\mathcal{O}$ with an $\mathcal{O}$-algebra automorphism $Fr$, complete for the $\pi$-adic topology (`hOnr_complete`), with $\pi\,Onr$ maximal (`hOnr_max`), such that every element of $Onr$ satisfies a monic polynomial over $\mathcal{O}$ modulo $\pi$ (`hOnr_alg`), every monic polynomial over $Onr$ of positive degree has a root modulo $\pi$ (`hOnr_closed`), and $Fr(x) \equiv x^r \pmod{\pi}$ (`hFr`); so $Onr/\pi$ is an algebraic closure of the residue field and $Fr$ lifts Frobenius. A homomorphism $\mathrm{vdet} : \mathrm{GL}_2(K_0) \to \mathbb{Z}$ (written multiplicatively) with $\mathrm{vdet}(g) = n$ if and only if $\det g = u\pi^n$ for some unit $u$ of $\mathcal{O}$ (`hvdet`).
--
--   **Quaternionic data.** Rationals $a, b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $a > 0$ or $b > 0$, and for a finite place $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes \mathbb{Q}_v$ is a division algebra exactly when $v$ lies over $r$ or over $\bar r$ (`hB`); a maximal order $\Lambda$ (`hΛ`, in the sense that $\Lambda$ is an order and is maximal among orders containing it); an element $\mu_\Lambda \in \Lambda$ with $\mu_\Lambda^2 = -(r\bar r)$ (`hμΛ`) and a map $\mathrm{star}_\Lambda$ on $\Lambda$ with $\mu_\Lambda \cdot \mathrm{star}_\Lambda(x) = \bar x \mu_\Lambda$ (`hstarΛ`); the assumption that $2$ is a unit in $\mathcal{O}$ (`h2`).
--
--   **Moduli frame.** A scheme $\mathcal{X}$ with $f : \mathcal{X} \to \operatorname{Spec}\mathcal{O}$ and a point map `pt` which is a coarse moduli datum for fake elliptic curves with level-$N$ structure over $\mathcal{O}$ (`h𝒳`: invariance under isomorphism, compatibility with base change, bijectivity on geometric points over algebraically closed fields, and the universal property). An auxiliary level $n \geq 3$ with $r \nmid n$, $\bar r \nmid n$ and $\gcd(n,N) = 1$ (`hn`, `hrn`, `hrbarn`, `hnN`), a scheme $M$ with $f_M$ and a point map `ptF` which is a fine moduli datum for pairs (fake elliptic curve, full level-$n$ structure) (`hM`), and a group $G$ acting by automorphisms $\rho$ of $M$ with labels $\chi : G \to \Lambda$ satisfying the level-twist axioms (`hρ`: the automorphisms lie over the base, they realise the twist of a level-$n$ structure by $\chi(g)$, and $\chi$ is multiplicative, surjective and injective modulo $n$). A forgetful morphism $p : M \to \mathcal{X}$ over the base (`hp`), invariant under $G$ (`hρp`), and compatible with the two point maps (`hp_pt`).
--
--   **Hecke and Atkin–Lehner structure.** For each prime $\ell$ distinct from $r$ and $\bar r$, a scheme $\mathcal{Y}_\ell$ over $\mathcal{O}$ with point map `ptT` which is a coarse moduli datum for curves with extra level $\ell$ (`h𝒴`), together with degeneracy maps $d_0(\ell), d_1(\ell) : \mathcal{Y}_\ell \to \mathcal{X}$ over the base (`hd₀f`, `hd₁f`) inducing on points the forgetting of the extra level (`hd₀`) and the passage to an $\ell$-level isogenous curve (`hd₁`). Endomorphisms $a_r, a_{\bar r}$ of $\mathcal{X}$ over the base (`harf`, `harbarf`) realising the Atkin–Lehner quotients at $r$ and at $\bar r$ on points (`har`, `harbar`).
--
--   **Definite quaternion side and the discrete group.** Rationals $a_1, b_1$ with $\mathbb{H}[\mathbb{Q},a_1,b_1]$ definite and ramified exactly at $\bar r$ (`hdef`), a maximal order $\Lambda_1$ (`hΛ₁`) and an Eichler order $R_1$ of level $N$ contained in it (`hR₁`, `hRΛ₁`), an adelic unit $n_1$ in the prime Hecke set of $R_1$ at $r$ (`hn₁`) such that $R_1 \cap n_1 R_1 n_1^{-1}$ is Eichler of level $Nr$ (`hS₁`), an injective $\mathbb{Q}$-algebra map $\iota_0 : \mathbb{H}[\mathbb{Q},a_1,b_1] \to M_2(K_0)$ (`hι₀`), and the place $v$ of $\mathbb{Q}$ above $r$ (`hv`). A subgroup $\Gamma_t$ of the units of $\mathbb{H}[\mathbb{Q},a_1,b_1]$ which coincides elementwise with the away-from-$v$ unit group of $R_1$ (`hΓt`); elements $s(\ell)$ and adelic units $sf(\ell)$ for each prime $\ell \neq r, \bar r$ whose local behaviour, Hecke-set membership (the `levelHeckeUSet` or `primeHeckeSet` of $R_1 \cap n_1 R_1 n_1^{-1}$ according to whether $\ell \mid N$) and reduced norm $\mathrm{nrd}(s(\ell)) = \ell$ are prescribed by `hs`; the subgroups $\Gamma_{t,\ell} = \Gamma_t \cap s(\ell)\Gamma_t s(\ell)^{-1}$ (`hΓtℓ`); and an element $\bar w$ of reduced norm $\bar r$ normalising $\Gamma_t$ (`hwbar`).
--
--   **The special fibre base point.** The hypothesis `hΛℤ` that every rational integer lies in $\Lambda$, and a coordinate map $\mathrm{coord} : \Lambda \to W(\mathbb{F}_{r^2})^2$ satisfying `IsOrderCoord` (additivity, $1 \mapsto (1,0)$, the Frobenius-twisted multiplication rule, injectivity, $r$-adic density and the trace rule). A fake elliptic curve $A_0$ over $Onr/\pi$, a formal $\mathcal{O}_D$-module $X_0$ over $Onr/\pi$ of height $4$ (`hX₀`), formal coordinates $\theta_0$ of dimension $2$ along the unit section of $A_0$, and the assertion `hA₀` that $A_0$ is a formal module via $\mathrm{coord}$, $X_0$, $\theta_0$. Endomorphism families $e, e' : \Gamma_t \to \mathrm{End}(A_0.A)$ with $e\gamma$ over the base (`he`) and exponents $\deg : \Gamma_t \to \mathbb{N}$, subject to: `hE1` ($e\gamma, e'\gamma$ form an isogeny pair of degree $r^{\deg\gamma}$ and $e\gamma$ preserves the level structure), `hE1mul` (multiplicativity of $e$ up to composing with $r$-power multiplications), `hE1sc` (scalars in $\Gamma_t$ are sent to scalar multiplications up to $r$-powers), `hE1'` (the converse: if $e\gamma$ becomes a positive integer multiplication after an $r$-power correction then $\gamma$ is a rational scalar), `hE2` (for every injective ring map $E_0$ from the centraliser of the $X_0$-action and $\varpi$ into $M_2(K_0)$ there is $g \in \mathrm{GL}_2(K_0)$ such that each $e\gamma$ is induced on formal coordinates by an element $\varepsilon$ of that centraliser with $E_0(\varepsilon) = r^{k_\gamma}\, g\,\iota_0(\gamma)\,g^{-1}$), `hE3` (existence, for each full level-$n$ structure $P_0$ on $A_0$, of a labelling $\mathrm{lab} : \Gamma_t \to \Lambda$ describing the action of $e\gamma$ on $P_0$, multiplicative and scalar-compatible modulo $n$), and `hE4` (every $r$-power isogeny self-map preserving the level on a curve over an algebraically closed field obtained from $A_0$ by base change comes from some $e\gamma$ up to $r$-power multiplications).
--
--   **The Eichler-order endomorphisms.** An order $R_2 \subseteq R_1$ (`hR₂`, `hR₂o`) with $r$-power saturation property (`hR₂r`), a family $\hat e : R_2 \to \mathrm{End}(A_0.A)$ over the base (`hê`), and hypotheses `hE5a` (each $\hat e(x)$ respects the group law, commutes with the $\Lambda$-action and preserves the level), `hE5b1`, `hE5b2`, `hE5b3` (unit, multiplicativity and compatibility with integer multiplications), `hE5c` ($\hat e(\bar x)$ followed by $\hat e(x)$ is multiplication by $\mathrm{nrd}(x)$), `hE5d` (compatibility of $\hat e$ with $e$ on $r$-power multiples of elements of $\Gamma_t$), and `hE5e` (the joint form of `hE2` for $\Gamma_t$ and for $R_2$ with one and the same conjugating $g$).
--
--   **The special formal moduli package.** A ring map $\iota : W(\mathbb{F}_{r^2}) \to Onr$, a formal $\mathcal{O}_D$-module $\Phi$ over $Onr/(r)$ which is special relative to $\iota$ (`hΦ`) and of height $4$ (`hΦ4`); a moduli package $MD$ over $Onr$ which is a Zariski sheaf (`hMD`); a map $\eta$ from rigidified objects of $\Phi$ to $MD$ with the three properties `hη` ($\eta$ identifies admissible rigidified objects exactly up to isomorphism, is natural in the base, and is surjective after passage to a Zariski cover by admissible objects); an injective ring map $E_0$ from the centraliser of the action of $\Phi$ and of $\varpi$ into $M_2(K_0)$ whose image is commensurable with $M_2(\mathcal{O})$ in the precise sense of `hE₀`.
--
--   **The Drinfeld comparison.** A family of maps $eD$ from the points of the functor $\mathrm{ModuliPackage.G}\,\mathcal{O}\,MD$ to pairs (an $\mathcal{O}$-algebra map from $Onr$, a Deligne datum for $(K_0,\pi)$), natural in the base (`hnatD`), bijective on every Noetherian $\mathcal{O}$-algebra with $\pi$ nilpotent (`hbijD`), compatible with the first components (`hfstD`), intertwining the $\mathrm{GL}_2(K_0)$-action on the package with the twisted action `OmegaNr.IsTwistedAct` on pairs (`hGLD`), sending $\pi$-translations to Frobenius twists of the first component (`hPiD`), with $\pi$-translates always existing (`hPiexD`); and the boundedness hypothesis `hbdd`: for every pair of full lattices $M' \subseteq M$ in $K_0^2$ with $\pi M \subseteq M'$ there is $N_\gamma$ such that, over an Artinian local Noetherian $\mathcal{O}$-algebra with algebraically closed residue field and $\pi$ nilpotent, every point whose Deligne datum lies in the edge chart of $(M', M)$ comes from an admissible rigidified object $t$ with $t.n \leq N_\gamma$.
--
--   **Transport data.** A ring map $\kappa : Onr/\pi \to Onr/(r)$ compatible with the quotient maps (`hκ`), a natural number $n_0$ and a series $\beta_0$ which is an isogeny of height $4n_0$ from $\Phi$ to the reduction of $X_0$ along $\kappa$ (`hβ₀`); a full level-$n$ structure $P_0$ on $A_0$.
--
--   **Atkin–Lehner at $\bar r$ on the base point.** A further curve $A_{0w}$ over $Onr/\pi$ with morphisms $a_w, a_w', b_w, b_w'$ over the base (`haw`, `haw'`, `hbw`, `habw`) and an exponent $k_w$, such that $(a_w, a_w')$ realises the Atkin–Lehner quotient at $\bar r$ (`hALw`), $(b_w, b_w')$ is an isogeny pair of degree $r^{k_w}$ (`hBSw`) with $b_w$ preserving the level (`hBSwlev`), and `hJOINTw`: for every injective $E_0$ as above there is one $g$ conjugating simultaneously all $e\gamma$ to $\iota_0(\gamma)$ and the composite $a_w$ followed by $b_w$ to $\iota_0(\bar w)$, each up to an $r$-power.
--
--   **The rigidified-to-$G$ map.** A map $\Xi$ sending a rigidified curve over a Noetherian $\mathcal{O}$-algebra $B$ with $\pi$ nilpotent to a point of $\mathrm{GPoint}$ of $MD$, with: `hΞleg` (over a connected base the structure map of $\Xi$ is a Frobenius twist of the given $\psi$), `hΞnat` (naturality under pullback of rigidified curves), `hΞiso` (invariance under isomorphisms of rigidified data up to $r$-power multiplications), and `hΞdef` (an explicit description: for a curve with formal module structure there are $j \leq 1$ and an admissible rigidified object $t$ with $t.X = X$, transported from $\theta_0$, $\kappa$, $\beta_0$, such that $\Xi$ is the triple built from the $(-j)$-th Frobenius twist of $\psi$ and $\eta(t)$). An element $g_0 \in \mathrm{GL}_2(K_0)$ and the equivariance hypotheses `heqΓ` and `heqW`: a translation of a rigidification by $e\gamma$, respectively an Atkin–Lehner quotient at $\bar r$ matched with $a_w$ followed by $b_w$, is carried by $\Xi$ into the action of $r^c\,g_0\,\iota_0(\gamma)\,g_0^{-1}$, respectively $r^c\,g_0\,\iota_0(\bar w)\,g_0^{-1}$, for some $c \in \mathbb{Z}$.
--
--   **The local chart.** A Noetherian $\mathcal{O}$-algebra $C$ with $\pi$ nilpotent (`hCπ`) and a map $\chi_C : Onr \to C$ of $\mathcal{O}$-algebras; a functor $PR$ on $C$-algebras with a point map `ptR` attached to pairs (full level-$n$ structure, rigidification) over $C$-algebras that are $\mathcal{O}$-algebras in a compatible way, subject to `hR2` (naturality under pullback), `hR3s` (surjectivity), `hR3i` (injectivity up to isomorphism of the rigidified data over a connected base) and `hR1` (its converse); a natural transformation $\theta$ from $PR$ to the Deligne-datum functor (`hθnat`) given on points by the pullback under $g_0^{-1}$ of the datum attached by $eD \circ \Xi$ (`hθ`); a map `toM` to the points of the pullback of $f_M$ along $\operatorname{Spec} C \to \operatorname{Spec}\mathcal{O}$, natural (`hR0`) and compatible with `ptF` (`hR4`); the sheaf property `hsh` (unique gluing of $PR$-points along a Zariski cover by localisations), the lifting property `het'` (unique lifting of $PR$-points along a surjection with square-zero kernel, prescribed compatibly with `toM`), and `hred` (the same for reduction modulo $\pi$).
--
--   **The stratification.** Schemes $X_d$ with morphisms $\xi_d$ to the pullback of $f_M$, locally of finite presentation (`hξ`) and formally unramified (`hunrξ`); point maps `pts` from $T$-points of $X_d$ to $PR(T)$ and `ptX` producing $T$-points of $X_d$ from a full level-$n$ structure together with a rigidification of exponent $d$ over a $T$ in which $\pi$ vanishes, subject to `hs0` (any $T$-point of $X_d$ forces $\pi = 0$ in $T$), `hs1` (compatibility of `pts` with `toM` and $\xi_d$), `hs2` (naturality of `pts`), `hx1` (`pts` applied to `ptX` returns `ptR`), `hx2` (naturality of `ptX`), `hx3` (surjectivity of `ptX`), `hx4` (the exact criterion for two `ptX`-points to coincide: an isomorphism of the level-$n$ data together with comparison maps $ib$, $uA$ satisfying $ib$ followed by $\rho'.\varphi$ followed by $uA$ equals $\rho.\varphi$), and `hs4` (a `ptR`-point lies in the image of `pts` for $d$ exactly when the curve carries a rigidification of exponent $d$ with the same `ptR`-point). Finally an element $g_\pi \in \mathrm{GL}_2(K_0)$ equal to the diagonal matrix $\mathrm{diag}(\pi,1)$ (`hgπ`), and a natural number $D$.
--
--   **Conclusion.** There exist an open subset $B$ of $X_D$ and a natural number $c$ with $c \geq 2$ such that for every nontrivial Noetherian ring $T$ which is a $C$-algebra and an $\mathcal{O}$-algebra compatibly, with $\operatorname{Spec} T$ connected (every idempotent of $T$ is $0$ or $1$) and with $\pi$ mapping to $0$ in $T$, there is a function $\deg_\varphi$ assigning a natural number to each morphism $E.A \to A.A$ between fake elliptic curves $E$, $A$ with level-$N$ structure over $T/\pi T$, for which the following six assertions hold, where $\rho$ always denotes a rigidification of a curve $E$ over $T$ relative to $A_0$ along the $\mathcal{O}$-algebra map $Onr \to T$ obtained from $\chi_C$, with components $\rho.\varphi : \rho.E_b.A \to \rho.A_b.A$ and $\rho.\varphi'$ forming an isogeny pair of degree $r^{\rho.d}$:
--
--   1. $\deg_\varphi \rho.\varphi > 0$ and $\deg_\varphi \rho.\varphi' > 0$;
--
--   2. $\deg_\varphi \rho.\varphi \cdot \deg_\varphi \rho.\varphi' = c^{\rho.d}$;
--
--   3. for every $i$, $\deg_\varphi$ of $\rho.\varphi$ followed by multiplication by $r^i$ on $\rho.A_b$ equals $c^i \deg_\varphi \rho.\varphi$, and $\deg_\varphi$ of multiplication by $r^i$ followed by $\rho.\varphi'$ equals $c^i \deg_\varphi \rho.\varphi'$;
--
--   4. (comparison law) for all level-$n$ data $u, u'$ over $T$ with rigidifications $\rho, \rho'$, every isomorphism $i$ of the underlying curves over the base which respects the group law, the $\Lambda$-action, the level and the level-$n$ section (`IsoVia`), every $ib : \rho.E_b.A \to \rho'.E_b.A$ compatible with the reductions $gb$ and with the base, every $uA : \rho'.A_b.A \to \rho.A_b.A$ which is a pullback along the identity and compatible with the maps $gA$, and all $i_1, j_1$ such that $ib$ followed by $\rho'.\varphi$, then $uA$, then multiplication by $r^{i_1}$ equals $\rho.\varphi$ followed by multiplication by $r^{j_1}$, one has $\deg_\varphi \rho'.\varphi \cdot c^{i_1} = \deg_\varphi \rho.\varphi \cdot c^{j_1}$;
--
--   5. (cancellation) with the same data and the same exponent $i_1$ on both sides, that is $ib$ followed by $\rho'.\varphi$, $uA$ and multiplication by $r^{i_1}$ equal to $\rho.\varphi$ followed by multiplication by $r^{i_1}$, one has $ib$ followed by $\rho'.\varphi$ and $uA$ equal to $\rho.\varphi$;
--
--   6. (window criterion) for every level-$n$ datum $u$ over $T$ and every rigidification $\rho$ of its curve with $\rho.d = D$, the $T$-point `ptX` $D$ attached to $(u,\rho)$ maps every point of $\operatorname{Spec} T$ into $B$ if and only if $\deg_\varphi \rho.\varphi \leq \deg_\varphi \rho.\varphi' < c^2 \cdot \deg_\varphi \rho.\varphi$.
--
--   This is the degree-theoretic ingredient of the Čerednik–Drinfeld uniformisation of the Shimura curve attached to an indefinite quaternion algebra ramified at $r$ and $\bar r$: it produces, on the stratum of rigidifications of exponent $D$, a locally constant degree invariant for the isogenies occurring in a rigidification together with the ratio window $\deg\varphi \le \deg\varphi' < c^2\deg\varphi$ cutting out an open subset of that stratum. It is used by the statement [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isOpenImmersion_stratum_window_of_rigidifiedToG_of_bdd_local`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isOpenImmersion_stratum_window_of_rigidifiedToG_of_bdd_local), where the window open is shown to be an open immersion chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian
open LT.LatticeTree (FullLattice)

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_opens_ratioWindow_degree_laws_of_rigidifiedToG_of_bdd

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

    (μΛ : ↥Λ) (hμΛ : (μΛ : ℍ[ℚ, a, b]) * (μΛ : ℍ[ℚ, a, b]) = -(((r * rbar : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (starΛ : ↥Λ → ↥Λ) (hstarΛ : ∀ x : ↥Λ, (μΛ : ℍ[ℚ, a, b]) * (starΛ x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μΛ)
    (h2 : IsUnit ((2 : ℕ) : 𝒪))
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

      (hbdd : ∀ (M' M : FullLattice 𝒪 K₀), M'.1 ≤ M.1 → (∀ v ∈ M.1, algebraMap 𝒪 K₀ π • v ∈ M'.1) →
        ∃ Nγ : ℕ, ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsArtinianRing B]
          [IsAlgClosed (IsLocalRing.ResidueField B)] [Algebra 𝒪 B]
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (ModuliPackage.G 𝒪 MD).obj B),
          DeligneDatum.InEdgeChart π (eD B hB y).2 M' M →
            ∃ t : Rigidified r Φ B, t.IsAdmissible ι (y.ψ : Onr →+* B) ∧ η B (y.ψ : Onr →+* B) y.nilp t = y.pt ∧ t.n ≤ Nγ)

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

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hCπ : IsNilpotent (algebraMap 𝒪 C π)) (χC : Onr →ₐ[𝒪] C)
    (PR : CerednikDrinfeld.FormalOmega.AlgFunctor C)
    (ptR : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (ψS : Onr →ₐ[𝒪] S) (_ : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S), FakeEllipticCurve.Rigidification r π A₀ ψS u.1 →
          PR.obj S)

    (hR2 : (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp χC)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
          (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
          (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
          FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
            PR.map φ (ptR S ψS hψS u ρ) = ptR S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ'))

    (hR3s : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (z : PR.obj S),
          ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1), ptR S ψS hψS u ρ = z))
    (hR3i : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (hSc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1),
          ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ' →
            ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
              ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

    (hR1 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1)
          (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
          FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi →
          (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ'))

    (θ : (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
        PR.obj S → (Omega K₀ π).obj S))
    (hθnat : (∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
          (g : S →ₐ[C] S') (x : PR.obj S),
          θ S' (PR.map g x) = (Omega K₀ π).map (g.restrictScalars 𝒪) (θ S x)))
    (hθ : (∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (hS : IsNilpotent (algebraMap 𝒪 S π))
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
          θ S (ptR S ψS hψS u ρ) = DeligneDatum.pullback π S (g₀⁻¹)⁻¹ (eD S hS (Ξ S ψS hS ⟨u.1, ρ⟩)).2))

    (toM : ∀ (S : Type) [CommRing S] [Algebra C S],
        PR.obj S → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))

(hR0 : ∀ (S S' : Type) [CommRing S] [Algebra C S] [CommRing S'] [Algebra C S'] (φ : S →ₐ[C] S') (x : PR.obj S),
        (toM S' (PR.map φ x)).1 = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (toM S x).1)

(hR4 : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
        (toM S (ptR S ψS hψS u ρ)).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) =
          (ptF S (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 S))) u).1)

(hsh : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, PR.obj (B i)),
      (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          PR.map (ρ₁.restrictScalars C) (s i) = PR.map (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : PR.obj A, ∀ i, PR.map (IsScalarTower.toAlgHom C A (B i)) s₀ = s i)

(het' : ∀ (S S₀ : Type) [CommRing S] [IsNoetherianRing S] [Algebra C S] [CommRing S₀] [Algebra C S₀] (p : S →ₐ[C] S₀),
        Function.Surjective p → RingHom.ker (p : S →+* S₀) ^ 2 = ⊥ →
        ∀ (x₀ : PR.obj S₀) (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
        Spec.map (CommRingCat.ofHom (p : S →+* S₀)) ≫ t.1 = (toM S₀ x₀).1 →
        ∃! x : PR.obj S, PR.map p x = x₀ ∧ toM S x = t)

(hred : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra C T]
        (xb : PR.obj (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))
        (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ t.1 =
          (toM _ xb).1 →
        ∃! x : PR.obj T,
          PR.map (Ideal.Quotient.mkₐ C (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) x = xb ∧ toM T x = t)
    (Xs : ℕ → Scheme.{0}) (ξ : ∀ d, Xs d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (hξ : ∀ d, LocallyOfFinitePresentation (ξ d)) (hunrξ : ∀ d, FormallyUnramified (ξ d))
    (pts : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T],
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) → PR.obj T)
    (ptX : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
            (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
            ρ.d = d → algebraMap C T (algebraMap 𝒪 C π) = 0 → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))

(hs0 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            algebraMap C T (algebraMap 𝒪 C π) = 0)

(hs1 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            (toM T (pts d T x)).1 = x.1 ≫ ξ d)

(hs2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
            (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
            (x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T'))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
            x'.1 = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ x.1 → pts d T' x' = PR.map φ (pts d T x))

(hx1 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
              (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
              pts d T (ptX d T ψT hψT u ρ hd h0) = ptR T ψT hψT u ρ)

(hx2 : ∀ (d : ℕ) (T T' : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T')
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (hψT' : (φ.restrictScalars 𝒪).comp ψT = (IsScalarTower.toAlgHom 𝒪 C T').comp χC)
              (u : FakeEllipticCurve.WithFullLevel Λ N n T) (u' : FakeEllipticCurve.WithFullLevel Λ N n T')
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
              (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψT) u'.1)
              (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : T →+* T') u.1 u'.1 g)
              (hd : ρ.d = d) (hd' : ρ'.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (h0' : algebraMap C T' (algebraMap 𝒪 C π) = 0),
              (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (u.2.P).1 →
              FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
                (ptX d T' ((φ.restrictScalars 𝒪).comp ψT) hψT' u' ρ' hd' h0').1 =
                  Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ (ptX d T ψT hψT u ρ hd h0).1)

(hx3 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
              ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                ptX d T ψT hψT u ρ hd h0 = x)

(hx4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
              (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
              (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0)
              (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
              (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u'.1)
              (hd : ρ.d = d) (hd' : ρ'.d = d),
              (ptX d T ψT hψT u ρ hd h0 = ptX d T ψT hψT u' ρ' hd' h0 ↔
                ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
                  ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
                    (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA),
                    ib ≫ ρ'.φ ≫ uA = ρ.φ))

(hs4 : ∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
            (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
            algebraMap C T (algebraMap 𝒪 C π) = 0 →
            ((∃ x, pts d T x = ptR T ψT hψT u ρ) ↔
              ∃ (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψT u.1), ρ'.d = d ∧ ptR T ψT hψT u ρ' = ptR T ψT hψT u ρ))

    (gπ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hgπ : (gπ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (D : ℕ) :
    ∃ (B : (Xs D).Opens) (c : ℕ) (_ : 2 ≤ c),
      ∀ (T : Type) [CommRing T] [Algebra C T] [IsNoetherianRing T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T] [Nontrivial T]
        (_ : ∀ e : T, IsIdempotentElem e → e = 0 ∨ e = 1) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0),
        ∃ (degφ : ∀ {E A : FakeEllipticCurve Λ N (T ⧸ Ideal.span {algebraMap 𝒪 T π})}, (E.A ⟶ A.A) → ℕ),

          (∀ {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) E),
              0 < degφ ρ.φ ∧ 0 < degφ ρ.φ') ∧

          (∀ {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) E),
              degφ ρ.φ * degφ ρ.φ' = c ^ ρ.d) ∧

          (∀ {E : FakeEllipticCurve Λ N T} (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) E) (i : ℕ),
              degφ (ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) = c ^ i * degφ ρ.φ ∧
              degφ (ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ') = c ^ i * degφ ρ.φ') ∧

          (∀ (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
            (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1)
            (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u'.1)
            (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hI : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
            (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
            (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
            (i₁ j₁ : ℕ),
            ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ →
              degφ ρ'.φ * c ^ i₁ = degφ ρ.φ * c ^ j₁) ∧

          (∀ (u u' : FakeEllipticCurve.WithFullLevel Λ N n T)
            (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1)
            (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u'.1)
            (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) (hI : FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi)
            (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
            (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
            (i₁ : ℕ),
            ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ →
              ib ≫ ρ'.φ ≫ uA = ρ.φ) ∧

          (∀ (u : FakeEllipticCurve.WithFullLevel Λ N n T)
            (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) u.1) (hd : ρ.d = D),
            (∀ p : ↥(Spec (CommRingCat.of T)), (ptX D T ((IsScalarTower.toAlgHom 𝒪 C T).comp χC) rfl u ρ hd h0).1 p ∈ B) ↔
              (degφ ρ.φ ≤ degφ ρ.φ' ∧ degφ ρ.φ' < c ^ 2 * degφ ρ.φ)) := by sorry
