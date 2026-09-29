-- Prove2me | Theorems.Thm_CerednikDrinfeld_mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_one_zero_of_two_mul_dvd
-- name    : CerednikDrinfeld.mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_one_zero_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/0a9f6525-beba-5283-830e-c9e65c97ad01
-- title:
--   Mumford embedding read off from the function-field identification
-- statement:
--   Arithmetic data. Let $N$ be a non-zero squarefree natural number, let $q$ and $q'$ be primes with $q \nmid N$, $q' \nmid N$, $q' \neq q$ and $5 \le q$, $5 \le q'$, and let $D$ be a non-zero natural number divisible by $2Nqq'$. Let $A_1$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $q'$ in the sense that $q'$ is a non-unit of $A_1$, and assume (as a `Fact`) that $A_1$ is decomposition-isometric over $\mathbb Q$, i.e. every element of the decomposition subgroup of $A_1$ over $\mathbb Q$ preserves the valuation of $A_1$. Let $v_1$ be a height-one prime of $\mathcal O_{\mathbb Q} = \mathbb Z$ containing $q'$.
--
--   The definite side. Let $a_2, b_2 \in \mathbb Q$ satisfy `IsDefiniteRamifiedExactlyAt q`: $a_2 < 0$, $b_2 < 0$, and for a height-one prime $v$ the completion $\mathbb H[\mathbb Q,a_2,b_2] \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra exactly when $q \in v$. Let $\Lambda_2$ be a maximal order and $R_2$ an Eichler order of level $N$ (an intersection of two maximal orders of relative index $N$) in $\mathbb H[\mathbb Q,a_2,b_2]$, with $R_2 \le \Lambda_2$. Let $n_2$ be a finite-idelic unit in the prime Hecke set `primeHeckeSet R₂ q'`. The hypotheses on $n_2$ are: `hS₂`, that `meetOrder R₂ n₂` $= R_2 \cap n_2 R_2 n_2^{-1}$ is an Eichler order of level $Nq'$; `hnorm₂`, that conjugation by $n_2$ fixes this order; `hsq₂`, that the shift by $n_2$ on the class set of the finite-idelic stabiliser of this order is an involution; and `hlaws₂`, the predicate `ClassSetHeckeLaws N q' Λ₂ R₂ n₂` asserting that the edge Hecke matrices commute with one another, that the vertex Hecke matrices commute with one another, that for primes $\ell \neq q$ the two degeneracy maps intertwine edge and vertex Hecke operators, and that the degeneracy maps carry the kernel of the joint degeneracy into itself under all edge Hecke operators. Finiteness and decidability of the relevant class sets are assumed.
--
--   The indefinite side and the moduli tower over $\mathbb Z[1/D]$. Let $a, b \in \mathbb Q$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'` ($0 < a$ or $0 < b$, and the completion at $v$ is a division algebra exactly when $q \in v$ or $q' \in v$), and let $\Lambda$ be a maximal order in $\mathbb H[\mathbb Q,a,b]$. Let $\bar F$ be a field which is a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` (principal divisors of degree zero exist, residue fields of places are finite over $\overline{\mathbb Q}$, and $\Omega_{\bar F/\overline{\mathbb Q}}$ is free of rank one) and essentially of finite type over $\overline{\mathbb Q}$. Let $\pi_X : X \to \operatorname{Spec} \mathbb Z[1/D]$ (the localisation away from $D$) be a scheme over that base, $\bar s$ a $\overline{\mathbb Q}$-point of the base, and `pt` an assignment, to each ring $S$, each $S$-point $s$ of the base and each fake elliptic curve of level $N$ for $\Lambda$ over $S$, of a point of $X$ over $s$; the hypotheses `pt_iso`, `pt_pullback`, `pt_surjective`, `pt_injective` are exactly the four non-universal coarse-moduli clauses for this assignment (invariance under isomorphism, compatibility with base change along ring maps, and bijectivity on isomorphism classes over algebraically closed fields). Let $\mathfrak M$ be a curve model of $\bar F$ over $\overline{\mathbb Q}$, let $e_{\mathfrak M}$ be an isomorphism from $\mathfrak M.C$ to the fibre product of $\pi_X$ and $\bar s$ whose composite with the second projection is the structure map of $\mathfrak M$, let `gal` be a homomorphism from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to the semilinear automorphisms of $\bar F$ over $\overline{\mathbb Q}$, let $\mathbb T$ be tower data of type `HeckeTower.TowerData q q'` over $\bar F$ (fields $\mathbb T.F(\ell)$ for primes $\ell \notin \{q,q'\}$, each a curve over $\overline{\mathbb Q}$, with two finite integral embeddings $\mathbb T.\varphi(\ell,k)$ of $\bar F$), let `galT` be Galois actions on the tower fields, and let $W : \mathrm{Fin}\,2 \to$ semilinear automorphisms of $\bar F$ and $WT$ the analogous data on the tower fields. Finally `tw` is a witness of `ModuliTowerWitnessD Λ N q q' D …`, tying places of $\bar F$ and of the tower fields to fake elliptic curves with and without extra level, fixing the base actions of `gal`, `galT`, $W$, $WT$, and identifying the degeneracy maps of the tower with level restriction and level isogeny.
--
--   Local data at $q'$. Let $\iota_1$ be an injective $\mathbb Q$-algebra embedding of $\mathbb H[\mathbb Q,a_2,b_2]$ into $M_2$ of the rational closure of $A_1$ inside the completion $\widehat{A_1}$ of the valuation, and let $\rho_1$ be the homomorphism from $\mathbb H[\mathbb Q,a_2,b_2]^{\times}$ to $\mathrm{PGL}_2$ of that ring obtained from $\iota_1$ (hypothesis `hρ₁`). Let $\varpi_1$ be a pseudo-uniformizer whose element maps to $q'$ in $\widehat{A_1}$, and assume the holomorphic ring `HolRingOf ϖ₁ ρ₁` is a domain. Let $\chi$ be a homomorphism from the decomposition subgroup of $A_1$ over $\mathbb Q$ to $\mathbb Z/2$ (multiplicatively written) which is trivial on inertia (`hχ₁`), non-trivial on every Frobenius element at $q'$ (`hχ₂`), and satisfies $\chi(\tau) = 1$ if and only if $\tau$ fixes every element $x$ of the residue field of $A_1$ with $x^{q'^2} = x$ (`hχ₃`). Let `dIso₁` be a homomorphism from the decomposition subgroup to the isometric automorphisms of $\widehat{A_1}$ realising the Galois action (`hdIso₁`). Let $\mathcal O_0$ be a complete discrete valuation ring of characteristic zero with uniformiser $\pi$, residue field of cardinality $q'$ and $(q') = (\pi)$, whose fraction field is the rational closure of $A_1$; let $O^{\mathrm{nr}}$ be a characteristic-zero domain over $\mathcal O_0$ with an $\mathcal O_0$-automorphism $\mathrm{Fr}$, $\pi$-adically complete, with $(\pi)$ maximal, integral over $\mathcal O_0$ modulo $\pi$ (`hOa`), such that every monic polynomial of positive degree has a root modulo $\pi$ (`hOcl`), and with $\mathrm{Fr}(x) \equiv x^{q'} \pmod \pi$ (`hFr`). Let `vdet` be a homomorphism $\mathrm{GL}_2 \to \mathbb Z$ (multiplicative) characterised by `hvdet` as the $\pi$-adic valuation of the determinant, and let $\psi_0 : O^{\mathrm{nr}} \to \widehat{A_1}$ be a ring map with $\pi \mapsto \varpi_1$ (`hπϖ`), $N$ invertible in $\mathcal O_0$ (`hN₀`), $\mathcal O_0$ the valuation ring of the rational closure (`h𝒪₀`), $\psi_0$ of valuation at most one (`hψ₀`), $\psi_0$ compatible with the structure maps (`hψ₀𝒪`), and with the value group Archimedean in the sense of `hrk`.
--
--   Group-theoretic data. For each prime $\ell \notin \{q,q'\}$ let $s_1(\ell) \in \mathbb H[\mathbb Q,a_2,b_2]^{\times}$ and $sf_1(\ell)$ a finite idele; `hs₁` requires that $sf_1(\ell)$ equals $s_1(\ell) \otimes 1$ at every place not above $q'$, equals $1$ at every place above $q'$, that the diagonal idele of $\ell$ times $sf_1(\ell)^{-1}$ lies in `levelHeckeUSet Λ₂ (meetOrder R₂ n₂) ℓ` if $\ell \mid N$ and in `primeHeckeSet (meetOrder R₂ n₂) ℓ` otherwise, and that $\mathrm{nrd}(s_1(\ell)) = \ell$. Let $\Gamma_1$ be a family of subgroups of $\mathbb H[\mathbb Q,a_2,b_2]^{\times}$ indexed by $\mathrm{Option}$ of the primes away from $q,q'$, with $\Gamma_1(\mathrm{none})$ consisting of those units lying in `awayUnits R₂ v₁` (image at every place $w \neq v_1$ in the subgroup generated by the local unit box of $R_2$) whose reduced norm has even $q'$-adic valuation (`hΓ₁0`), and $\Gamma_1(\mathrm{some}\,\ell) = \Gamma_1(\mathrm{none}) \cap s_1(\ell)\Gamma_1(\mathrm{none})s_1(\ell)^{-1}$ (`hΓ₁ℓ`). Let $w_1$ and $\bar w_1$ be further families of units: `hw₁` requires $w_1(\mathrm{none}) \in$ `awayUnits R₂ v₁` with reduced norm $q'$, and $w_1(\mathrm{some}\,\ell) \in$ `awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁` with reduced norm $q'$; `hwbar₁` requires $\bar w_1(\mathrm{none})$ to have reduced norm $q$, to lie in the local unit box of $R_2$ at every place $w \neq v_1$ not above $q$, and to normalise both the local box of $R_2$ and that of $\Lambda_2$ at every place $w \neq v_1$, together with the same three conditions for $\bar w_1(\mathrm{some}\,\ell)$ with $R_2$ replaced by `meetOrder R₂ (sf₁ ℓ)`.
--
--   The integral model and its Hecke and Atkin–Lehner structure. Let $f_0 : \mathcal X_0 \to \operatorname{Spec} \mathcal O_0$ together with `pt₀` be a coarse moduli space `IsCoarseModuli Λ N 𝒳₀ f₀ pt₀` for fake elliptic curves of level $N$, with $\mathcal X_0$ integral and $f_0$ flat, separated, locally of finite type and quasi-compact; for each prime $\ell$ away from $q'$ and $q$ let $g_0(\ell) : \mathcal Y_0(\ell) \to \operatorname{Spec} \mathcal O_0$ with `ptT₀` be a coarse moduli space `IsCoarseModuliT Λ N ℓ …` for such curves with extra level structure of order $\ell$, and let $d_{0}(\ell), d_{1}(\ell) : \mathcal Y_0(\ell) \to \mathcal X_0$ be morphisms over the base (`hd₀f`, `hd₁f`) realising, on moduli points, forgetting the extra level (`hd₀`) and passing to an $\ell$-level isogeny (`hd₁`). Let $a, \bar a$ (Lean: `ar`, `arbar`) be endomorphisms of $\mathcal X_0$ over the base (`harf`, `harbarf`) realising on moduli points the Atkin–Lehner quotient at $q'$ (`har`) and at $q$ (`harbar`).
--
--   The Čerednik–Drinfeld uniformisation. Let $\Theta$ and $\Theta_T(\ell)$ assign, to each $\mathcal O_0$-algebra $B$ in which $\pi$ is nilpotent, maps from the set of pairs consisting of an $\mathcal O_0$-algebra map $O^{\mathrm{nr}} \to B$ and a Deligne datum (a point of the formal upper half-plane functor `FormalOmega.Omega` at $\pi$) to the nilpotent points of $f_0$, respectively of $g_0(\ell)$. The hypothesis `hCD` is a conjunction of ten clauses, summarised here: naturality of $\Theta$ and of each $\Theta_T(\ell)$ in $B$; invariance of $\Theta$ under the twisted action `OmegaNr.IsTwistedAct` of the elements of `awayUnits R₂ v₁` and of $\Theta_T(\ell)$ under that of `awayUnits R₂ v₁` intersected with its $s_1(\ell)$-conjugate; over an algebraically closed field $k$ with $\pi$ nilpotent and a fixed $\psi$, surjectivity of $\Theta(\psi,\cdot)$ and of $\Theta_T(\ell)(\psi,\cdot)$ onto the nilpotent points, with two points having the same image exactly when they are in one orbit of the corresponding twisted action; the universal property of $\Theta$ and of each $\Theta_T(\ell)$ as the initial invariant map to nilpotent points of any base scheme; compatibility of $\Theta_T(\ell)$ with $d_0(\ell)$ (equality with $\Theta$) and with $d_1(\ell)$ (equality with $\Theta$ after the twisted action of $s_1(\ell)$); and compatibility of $a$ with the Frobenius twist `frobTwist Onr Fr 1` in the first coordinate, and of $\bar a$ with the twisted action of $\bar w_1(\mathrm{none})$. Here the indexing of the moduli tower by primes away from $q'$ and $q$ is matched with the indexing of the group-theoretic data by primes away from $q$ and $q'$ through the evident swap. The base changes of $f_0$ and of each $g_0(\ell)$ along the composite $\mathcal O_0 \to$ rational closure $\to \widehat{A_1}$ are assumed integral.
--
--   The function-field read-off hypothesis `hGF`. There exists an isomorphism $e$ from the function field of the base change of $f_0$ to $\widehat{A_1}$ onto the field `Mumford.invariantFieldOf` of $\Gamma_1(\mathrm{none})$-invariants inside the fraction field of `HolRingOf ϖ₁ ρ₁`, such that: $e$ carries constants from $\widehat{A_1}$ to constants; for every endomorphism $a_X$ of $\mathcal X_0$ over the base and every $g \in \mathbb H[\mathbb Q,a_2,b_2]^{\times}$ with $\mathrm{vdet}(\iota_1 g) = 1$ which $\Theta$-intertwines $a_X$ with the twisted action of $g$, any lift $a_{XC}$ of $a_X$ to the base change acts on germs at the generic point by $g^{-1} \cdot$; for every endomorphism $b_X$ $\Theta$-intertwined with the Frobenius twist by $1$, and every $w \in$ `awayUnits R₂ v₁` with $\mathrm{vdet}(\iota_1 w) = 1 \in \mathbb Z$, any lift $b_{XC}$ acts by $w^{-1} \cdot$; for every isometric automorphism $s$ of $\widehat{A_1}$ and every $n \in \mathbb Z$ such that $s \circ \psi_0 = \psi_0 \circ \mathrm{Fr}^n$ on the $\mathrm{Fr}^2$-fixed elements, and every such $w$, any lift $t_C$ of $\operatorname{Spec}$ of $s$ acts by $w^n \cdot$ composed with the semilinear map `fracMap (toAmbientOf ϖ₁ ρ₁ s)`; and for each $\ell$ an analogous isomorphism $e_Y$ of the function field of the base change of $g_0(\ell)$ onto the $\Gamma_1(\mathrm{some}\,\ell)$-invariants, compatible with constants and transforming germs along any $\Theta$-intertwined morphism $\mathcal Y_0(\ell) \to \mathcal X_0$ by $g^{-1} \cdot$.
--
--   The embedding hypothesis `hj`. There is a ring homomorphism $j$ from $\bar F$ to the function field of the base change of $f_0$ such that: $j$ agrees with the constants from $\overline{\mathbb Q} \subset \widehat{A_1}$ on $\overline{\mathbb Q}$; the subfield generated by the constants and the image of $j$ is everything; any finite subset of $\bar F$ linearly independent over $\overline{\mathbb Q}$ admits no non-trivial vanishing relation with coefficients from $\widehat{A_1}$; any lift of $a$ to the base change transforms $j(x)$ into $j(W(1) \cdot x)$, and any lift of $\bar a$ transforms $j(x)$ into $j(W(0) \cdot x)$; for $\tau$ in the decomposition subgroup, any lift of $\operatorname{Spec}$ of `dIso₁ τ` transforms $j(x)$ into $j(\mathrm{gal}(\tau) \cdot x)$; and for each prime $\ell$ away from $q,q'$ there is $j_\ell : \mathbb T.F(\ell) \to$ the function field of the base change of $g_0(\ell)$ such that, for $k \in \{0,1\}$, any lift of $d_k(\ell)$ transforms $j(x)$ into $j_\ell(\mathbb T.\varphi(\ell,k)(x))$.
--
--   Conclusion. Under these hypotheses there exists a ring homomorphism $\iota_0 : \bar F \to \operatorname{Frac}(\mathrm{HolRingOf}\ \varpi_1\ \rho_1)$ such that:
--
--   1. for every $z \in \overline{\mathbb Q}$, $\iota_0$ of the image of $z$ in $\bar F$ is the image of $z \in \widehat{A_1}$ under the structure map of the fraction field;
--
--   2. the subfield generated by the image of $\widehat{A_1}$ together with the range of $\iota_0$ equals the field of $\Gamma_1(\mathrm{none})$-invariants `Mumford.invariantFieldOf` in that fraction field;
--
--   3. for every finite subset $t$ of $\bar F$ linearly independent over $\overline{\mathbb Q}$, the family $(\iota_0 x)_{x \in t}$ is linearly independent over $\widehat{A_1}$;
--
--   4. for every $\tau$ in the decomposition subgroup of $A_1$ over $\mathbb Q$ and every $x \in \bar F$,
--   $$\iota_0\bigl(\mathrm{gal}(\tau)\cdot x\bigr) = \bigl(\text{$1$ if } \chi(\tau) = 1,\ w_1(\mathrm{none}) \text{ otherwise}\bigr) \cdot \mathrm{fracMap}\bigl(\mathrm{toAmbientOf}\ \varpi_1\ \rho_1\ (\mathrm{dIso}_1 \tau)\bigr)(\iota_0 x);$$
--
--   5. $\iota_0(W(1) \cdot x) = w_1(\mathrm{none}) \cdot \iota_0 x$ for all $x \in \bar F$;
--
--   6. $\iota_0(W(0) \cdot x) = \bar w_1(\mathrm{none}) \cdot \iota_0 x$ for all $x \in \bar F$;
--
--   7. for every prime $\ell$ away from $q$ and $q'$ there is a ring homomorphism $\iota_\ell : \mathbb T.F(\ell) \to \operatorname{Frac}(\mathrm{HolRingOf}\ \varpi_1\ \rho_1)$ with $\iota_\ell(\mathbb T.\varphi(\ell,0)(x)) = \iota_0 x$ and $\iota_\ell(\mathbb T.\varphi(\ell,1)(x)) = s_1(\ell) \cdot \iota_0 x$ for all $x \in \bar F$.
--
--   In items 4–7 the action of $\mathbb H[\mathbb Q,a_2,b_2]^{\times}$ on the fraction field of the holomorphic ring is the one induced by $\rho_1$.
--
--   This is the read-off step of the Čerednik–Drinfeld uniformisation of the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$: from an identification of the function field of the base-changed integral model with the $\Gamma_1$-invariant functions on Mumford's rigid-analytic quotient, it produces the embedding of the abstract function field $\bar F$ into that field of invariants, together with the resulting dictionary between the Galois action, the two Atkin–Lehner involutions and the Hecke tower on one side, and multiplication by the units $w_1$, $\bar w_1$, $s_1(\ell)$ of the definite quaternion algebra on the other. It is used by [`CerednikDrinfeld.mumfordEmbedding_assembly_of_functionField_equiv_one_zero_of_two_mul_dvd`](thm.html#CerednikDrinfeld.mumfordEmbedding_assembly_of_functionField_equiv_one_zero_of_two_mul_dvd), which assembles these data into the comparison of the two quaternionic towers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_one_zero_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_CerednikDrinfeld_DescentIntertwiningBase
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.mumfordEmbedding_readoff_of_functionField_equiv_of_ringHom_one_zero_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')

    {a₂ b₂ : ℚ} (hdef₂ : IsDefiniteRamifiedExactlyAt (a := a₂) (b := b₂) q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (n₂ : (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₂ : n₂ ∈ primeHeckeSet R₂ q')
    (hS₂ : IsEichlerOrder (meetOrder R₂ n₂) (N * q'))
    (hnorm₂ : Submodule.conjByFiniteIdele (meetOrder R₂ n₂) n₂ = meetOrder R₂ n₂)
    (hsq₂ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)),
      classSetShift _ n₂ (classSetShift _ n₂ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    (hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)

    [hiso₁ : Fact (A₁.DecompositionIsometric ℚ)]
    (v₁ : HeightOneSpectrum (𝓞 ℚ)) (hv₁ : ((q' : ℕ) : 𝓞 ℚ) ∈ v₁.asIdeal)

    (ι₁ : ℍ[ℚ, a₂, b₂] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (hι₁ : Function.Injective ι₁)
    (ρ₁ : (ℍ[ℚ, a₂, b₂])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₁)))
    (hρ₁ : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, ρ₁ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) x))

    (ϖ₁ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hϖ₁ : algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion ϖ₁.ϖ = ((q' : AlgebraicClosure ℚ) : A₁.valuation.Completion))
    [hdom₁ : IsDomain (Omega.HolRingOf ϖ₁ ρ₁)]

    (s₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (sf₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₁ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₁ ℓ : ℍ[ℚ, a₂, b₂]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₂, b₂]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₁ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₂ (meetOrder R₂ n₂) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₂ n₂) (ℓ.1 : ℕ)) ∧
      nrd (s₁ ℓ : ℍ[ℚ, a₂, b₂]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₁ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₂, b₂])ˣ)
    (hΓ₁0 : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, x ∈ Γ₁ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ Even (padicValRat q' (nrd (x : ℍ[ℚ, a₂, b₂]))))
    (hΓ₁ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₁ (some ℓ) = Γ₁ none ⊓ (Γ₁ none).map (MulAut.conj (s₁ ℓ)).toMonoidHom)

    (w₁ wbar₁ : HeckeTower.Obj q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (hw₁ : (w₁ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ nrd (w₁ none : ℍ[ℚ, a₂, b₂]) = (q' : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₁ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁ ∧ nrd (w₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q' : ℚ))
    (hwbar₁ :
      (nrd (wbar₁ none : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₁ none) ∈ Submodule.localBoxUnits R₂ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox R₂ u ↔
            x ∈ Submodule.localBox R₂ u) ∧
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
            x ∈ Submodule.localBox Λ₂ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₁ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₂ (sf₁ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
              x ∈ Submodule.localBox Λ₂ u))))

    (dIso₁ : ↥(A₁.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hdIso₁ : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : A₁.valuation.Completion), (dIso₁ τ).toRingEquiv x = τ • x)

    (χ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (hχ₁ : (∀ τ : ↥(A₁.decompositionSubgroup ℚ), (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₁.inertiaSubgroupIn ℚ → χ τ = 1))
    (hχ₂ : (∀ φ : ↥(A₁.decompositionSubgroup ℚ), A₁.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q' → χ φ ≠ 1))
    (hχ₃ : (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χ τ = 1 ↔ ∀ x : IsLocalRing.ResidueField ↥A₁, x ^ (q' ^ 2) = x → τ • x = x))

    (𝒪₀ : Type) [CommRing 𝒪₀] [IsDomain 𝒪₀] [CharZero 𝒪₀] (hdvr₀ : IsDiscreteValuationRing 𝒪₀)
    (π : 𝒪₀) (hπ : Irreducible π) (hcpl : IsAdicComplete (Ideal.span {π}) 𝒪₀) (hres : Nat.card (𝒪₀ ⧸ Ideal.span {π}) = q')
    (hunr : Ideal.span {((q' : ℕ) : 𝒪₀)} = Ideal.span {π})
    [Algebra 𝒪₀ ↥(ValuationSubring.ratClosure A₁)] [IsFractionRing 𝒪₀ ↥(ValuationSubring.ratClosure A₁)]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪₀ Onr] (Fr : Onr ≃ₐ[𝒪₀] Onr)
    (hOc : IsAdicComplete (Ideal.span {algebraMap 𝒪₀ Onr π}) Onr)
    (hOm : (Ideal.span {algebraMap 𝒪₀ Onr π}).IsMaximal)
    (hOa : ∀ x : Onr, ∃ p : Polynomial 𝒪₀, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hOcl : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ q' ∈ Ideal.span {algebraMap 𝒪₀ Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₁) →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪₀ˣ, (Matrix.GeneralLinearGroup.det g : ↥(ValuationSubring.ratClosure A₁)) = algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁) (u : 𝒪₀) * (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁) π) ^ n)
    (ψ₀ : Onr →+* A₁.valuation.Completion)
    (hπϖ : algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁) π = ϖ₁.ϖ) (hN₀ : IsUnit ((N : ℕ) : 𝒪₀))
    (h𝒪₀ : ∀ x : ↥(ValuationSubring.ratClosure A₁), x ∈ Set.range (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)) ↔ Valued.v (algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion x) ≤ 1)
    (hψ₀ : ∀ y : Onr, Valued.v (ψ₀ y) ≤ 1)
    (hψ₀𝒪 : ψ₀.comp (algebraMap 𝒪₀ Onr) = (algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))
    (hrk : ∀ x y : A₁.valuation.Completion, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)), FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (h𝒳₀ : IsCoarseModuli Λ N 𝒳₀ f₀ pt₀) [IsIntegral 𝒳₀] [Flat f₀] [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (𝒴₀ : HeckeTower.AwayPrime q' q → Scheme.{0}) (g₀ : ∀ ℓ : HeckeTower.AwayPrime q' q, 𝒴₀ ℓ ⟶ Spec (CommRingCat.of 𝒪₀))
    (ptT₀ : ∀ (ℓ : HeckeTower.AwayPrime q' q) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g₀ ℓ))
    (h𝒴₀ : ∀ ℓ : HeckeTower.AwayPrime q' q, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴₀ ℓ) (g₀ ℓ) (ptT₀ ℓ))
    (d₀₀ d₁₀ : ∀ ℓ : HeckeTower.AwayPrime q' q, 𝒴₀ ℓ ⟶ 𝒳₀)
    (hd₀f : ∀ ℓ, d₀₀ ℓ ≫ f₀ = g₀ ℓ) (hd₁f : ∀ ℓ, d₁₀ ℓ ≫ f₀ = g₀ ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime q' q) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT₀ ℓ S s u).1 ≫ d₀₀ ℓ = (pt₀ S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime q' q) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT₀ ℓ S s u).1 ≫ d₁₀ ℓ = (pt₀ S s d).1)

    (ar arbar : 𝒳₀ ⟶ 𝒳₀) (harf : ar ≫ f₀ = f₀) (harbarf : arbar ≫ f₀ = f₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q' E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient q E E' → (pt₀ S s E).1 ≫ arbar = (pt₀ S s E').1)

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints f₀).obj B)
    (ΘT : ∀ ℓ : HeckeTower.AwayPrime q' q, ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints (g₀ ℓ)).obj B)
    (hCD :

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), Θ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints f₀).map φ (Θ B hB x)) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
          (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), ΘT ℓ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints (g₀ ℓ)).map φ (ΘT ℓ B hB x))) ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → Θ B hB x' = Θ B hB x) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁).map (MulAut.conj (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)).toMonoidHom) →
          ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → ΘT ℓ B hB x' = ΘT ℓ B hB x)) ∧

      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints f₀).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, Θ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
            ∃ γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) (ψ, P) (ψ, P')) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪₀ k] (hk : IsNilpotent (algebraMap 𝒪₀ k π)) (ψ : Onr →ₐ[𝒪₀] k),
          (∀ y : (Scheme.nilpPoints (g₀ ℓ)).obj k, ∃ P : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, ΘT ℓ k hk (ψ, P) = y) ∧
          ∀ P P' : (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π).obj k, ΘT ℓ k hk (ψ, P) = ΘT ℓ k hk (ψ, P') ↔
            ∃ γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁).map (MulAut.conj (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)).toMonoidHom), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) (ψ, P) (ψ, P'))) ∧

      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u B hB (Θ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints f₀).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints f₀).obj B), u' B' hB' ((Scheme.nilpPoints f₀).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u' B hB (Θ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints f₀).obj B), u' B hB y = u B hB y) ∧
      (∀ ℓ : HeckeTower.AwayPrime q' q, (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪₀))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
            (φ : B →ₐ[𝒪₀] B') (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), ρ B' hB' ((FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ⊓ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁).map (MulAut.conj (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)).toMonoidHom) →
            ∀ x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B, FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
              (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u B hB (ΘT ℓ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B], IsNilpotent (algebraMap 𝒪₀ B π) → (Scheme.nilpPoints (g₀ ℓ)).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (B' : Type) [CommRing B'] [Algebra 𝒪₀ B'] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (hB' : IsNilpotent (algebraMap 𝒪₀ B' π))
                (φ : B →ₐ[𝒪₀] B') (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B' hB' ((Scheme.nilpPoints (g₀ ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), u' B hB (ΘT ℓ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (y : (Scheme.nilpPoints (g₀ ℓ)).obj B), u' B hB y = u B hB y)) ∧

      (∀ (ℓ : HeckeTower.AwayPrime q' q) (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₀₀ ℓ) (hd₀f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q' q) (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
        FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) (s₁ ⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩)) x' x →
        (Scheme.nilpPoints.mapHom (g₀ ℓ) f₀ (d₁₀ ℓ) (hd₁f ℓ)).app B (ΘT ℓ B hB x) = Θ B hB x') ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
        (Scheme.nilpPoints.mapHom f₀ f₀ ar harf).app B (Θ B hB x) = Θ B hB (FormalOmega.frobTwist Onr Fr 1 x.1, x.2)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π)) (x x' : (FormalOmega.AlgFunctor.prod (FormalOmega.AlgFunctor.corep Onr) (FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B), FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) (wbar₁ none)) x x' →
        (Scheme.nilpPoints.mapHom f₀ f₀ arbar harbarf).app B (Θ B hB x) = Θ B hB x'))
    [hXCint : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))]
    [hYCint : ∀ ℓ : HeckeTower.AwayPrime q' q, IsIntegral (Limits.pullback (g₀ ℓ) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))]
    (hGF :
    ∃ _ : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))),
    ∃ e : ↑(Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).functionField ≃+* ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none)),

      (∀ c : A₁.valuation.Completion, e (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) c) =
        algebraMap A₁.valuation.Completion ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none)) c) ∧

      (∀ (aX : 𝒳₀ ⟶ 𝒳₀) (haX : aX ≫ f₀ = f₀) (g : (ℍ[ℚ, a₂, b₂])ˣ), vdet ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) g) = 1 →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π))
            (x x' : (CerednikDrinfeld.FormalOmega.AlgFunctor.prod (CerednikDrinfeld.FormalOmega.AlgFunctor.corep Onr) (CerednikDrinfeld.FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
            CerednikDrinfeld.FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) g) x x' → (Scheme.nilpPoints.mapHom f₀ f₀ aX haX).app B (Θ B hB x) = Θ B hB x') →
        ∀ (aXC : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))),
          aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ aX → aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
        ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0}) ∈ aXC ⁻¹ᵁ U) (s : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0})) hU').hom ((aXC.app U).hom s)) :
              ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            g⁻¹ • ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0})) hU).hom s) :
              ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧

      (∀ (bX : 𝒳₀ ⟶ 𝒳₀) (hbX : bX ≫ f₀ = f₀),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π))
            (x : (CerednikDrinfeld.FormalOmega.AlgFunctor.prod (CerednikDrinfeld.FormalOmega.AlgFunctor.corep Onr) (CerednikDrinfeld.FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
            (Scheme.nilpPoints.mapHom f₀ f₀ bX hbX).app B (Θ B hB x) = Θ B hB (CerednikDrinfeld.FormalOmega.frobTwist Onr Fr 1 x.1, x.2)) →
        ∀ (bXC : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))),
          bXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ bX → bXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
        ∀ (w : (ℍ[ℚ, a₂, b₂])ˣ), w ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁) → vdet ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) w) = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0}) ∈ bXC ⁻¹ᵁ U) (s : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (bXC ⁻¹ᵁ U) (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0})) hU').hom ((bXC.app U).hom s)) :
              ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            w⁻¹ • ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0})) hU).hom s) :
              ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧

      (∀ (s : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion) (n : ℤ),
        (∀ y : Onr, Fr (Fr y) = y → s.toRingEquiv (ψ₀ y) = ψ₀ ((Fr ^ n : Onr ≃ₐ[𝒪₀] Onr) y)) →
        ∀ (tC : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))),
          tC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
          tC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ Spec.map (CommRingCat.ofHom (s.toRingEquiv : A₁.valuation.Completion →+* A₁.valuation.Completion)) →
        ∀ (w : (ℍ[ℚ, a₂, b₂])ˣ), w ∈ (CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁) → vdet ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) w) = Multiplicative.ofAdd (1 : ℤ) →
        ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0}) ∈ U)
          (hU' : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0}) ∈ tC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
          ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (tC ⁻¹ᵁ U) (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0})) hU').hom ((tC.app U).hom sec)) :
              ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            w ^ n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ s)
              ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0})) hU).hom sec) :
                ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧

      (∀ i : (HeckeTower.AwayPrime q' q), ∃ _ : IsIntegral (Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))),
        ∃ eY : ↑(Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).functionField ≃+* ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) ((fun ℓ : HeckeTower.AwayPrime q' q => Γ₁ (some (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q q'))) i)),
          (∀ c : A₁.valuation.Completion, eY (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) c) =
            algebraMap A₁.valuation.Completion ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) ((fun ℓ : HeckeTower.AwayPrime q' q => Γ₁ (some (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q q'))) i)) c) ∧
          (∀ (h : 𝒴₀ i ⟶ 𝒳₀) (hhf : h ≫ f₀ = g₀ i) (g : (ℍ[ℚ, a₂, b₂])ˣ), vdet ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) g) = 1 →
            (∀ (B : Type) [CommRing B] [Algebra 𝒪₀ B] (hB : IsNilpotent (algebraMap 𝒪₀ B π))
                (x x' : (CerednikDrinfeld.FormalOmega.AlgFunctor.prod (CerednikDrinfeld.FormalOmega.AlgFunctor.corep Onr) (CerednikDrinfeld.FormalOmega.Omega ↥(ValuationSubring.ratClosure A₁) π)).obj B),
                CerednikDrinfeld.FormalOmega.OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁))) g) x x' →
                  (Scheme.nilpPoints.mapHom (g₀ i) f₀ h hhf).app B (ΘT i B hB x) = Θ B hB x') →
            ∀ (hC : Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ⟶ Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))),
              hC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ h →
              hC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
            ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0}) ∈ U)
              (hU' : genericPoint (Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0}) ∈ hC ⁻¹ᵁ U)
              (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
              ((eY (((Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (hC ⁻¹ᵁ U) (genericPoint (Limits.pullback (g₀ i) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0})) hU').hom
                  ((hC.app U).hom sec)) : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) ((fun ℓ : HeckeTower.AwayPrime q' q => Γ₁ (some (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q q'))) i))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
                g⁻¹ • ((e (((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) : Scheme.{0})) hU).hom sec) :
                  ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)))))
    (j : Fbar →+* ↑(Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).functionField)
    (hj :

      (∀ z : AlgebraicClosure ℚ, j (algebraMap (AlgebraicClosure ℚ) Fbar z) = (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))) ((z : AlgebraicClosure ℚ) : A₁.valuation.Completion)) ∧

      (Subfield.closure (Set.range (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))) ∪ Set.range j) = ⊤) ∧

      (∀ (t : Finset Fbar), LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : Fbar)) →
        ∀ c : t → A₁.valuation.Completion, (∑ x : t, (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))) (c x) * j (x : Fbar)) = 0 → ∀ x : t, c x = 0) ∧

      (∀ (aXC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))), aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ ar →
        aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ aXC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU').hom ((aXC.app U).hom sec) = j (W 1 • x)) ∧

      (∀ (aXC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))), aXC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ arbar →
        aXC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ aXC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (aXC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU').hom ((aXC.app U).hom sec) = j (W 0 • x)) ∧

      (∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (tC : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))),
        tC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
        tC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ Spec.map (CommRingCat.ofHom ((dIso₁ τ).toRingEquiv : A₁.valuation.Completion →+* A₁.valuation.Completion)) →
        ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ tC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (tC ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU').hom ((tC.app U).hom sec) = j ((gal.comp (A₁.decompositionSubgroup ℚ).subtype) τ • x)) ∧

      (∀ ℓ : HeckeTower.AwayPrime q q', ∃ jℓ : 𝕋.F ℓ →+* ↑(Limits.pullback (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).functionField,
        ∀ (k : Fin 2) (dC : (Limits.pullback (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) ⟶ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))))),
          dC ≫ Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.fst (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) ≫ (if k = 0 then d₀₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q) else d₁₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) →
          dC ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) = Limits.pullback.snd (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁))))) →
          ∀ x : Fbar, ∀ (U : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).Opens) (hU : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ U) (hU' : (genericPoint ((Limits.pullback (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) ∈ dC ⁻¹ᵁ U) (sec : (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.obj (Opposite.op U)),
            ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ U (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU).hom sec = j x →
            ((Limits.pullback (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))).presheaf.germ (dC ⁻¹ᵁ U) (genericPoint ((Limits.pullback (g₀ (⟨ℓ.1, ⟨ℓ.2.2, ℓ.2.1⟩⟩ : HeckeTower.AwayPrime q' q)) (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₁)))))) : Scheme.{0})) hU').hom ((dC.app U).hom sec) = jℓ (𝕋.φ (ℓ, k) x)))
    :
    ∃ ι₀ : Fbar →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁),
      (∀ z : AlgebraicClosure ℚ, ι₀ (algebraMap (AlgebraicClosure ℚ) Fbar z) =
          algebraMap A₁.valuation.Completion (FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) ((z : AlgebraicClosure ℚ) : A₁.valuation.Completion)) ∧
      (Subfield.closure (Set.range (algebraMap A₁.valuation.Completion (FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∪ Set.range ι₀) =
          Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ none)) ∧
      (∀ t : Finset Fbar, LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : Fbar)) →
          LinearIndependent A₁.valuation.Completion (fun x : t => ι₀ (x : Fbar))) ∧
      (∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : Fbar),
          ι₀ ((gal.comp (A₁.decompositionSubgroup ℚ).subtype) τ • x) =
            (if χ τ = 1 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else w₁ none) •
              Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ τ)) (ι₀ x)) ∧
      (∀ x : Fbar, ι₀ (W 1 • x) = w₁ none • ι₀ x) ∧
      (∀ x : Fbar, ι₀ (W 0 • x) = wbar₁ none • ι₀ x) ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', ∃ ιℓ : 𝕋.F ℓ →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁),
      (∀ x : Fbar, ιℓ (𝕋.φ (ℓ, 0) x) = ι₀ x) ∧ (∀ x : Fbar, ιℓ (𝕋.φ (ℓ, 1) x) = (s₁ ℓ) • ι₀ x)) := by sorry
