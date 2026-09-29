-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_descentIntertwiningBase_of_moduliTowerWitness_zero_one_of_two_mul_dvd
-- name    : CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_zero_one_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/8e620b55-471f-5295-ac07-00c456ff789d
-- title:
--   Descent intertwining datum at q from a moduli tower witness
-- statement:
--   Throughout, $q$ and $q'$ are primes, $N \ge 1$ is an integer, and the data fall into the groups named below; the conclusion is stated in full at the end.
--
--   **Numerical data.** $N$ is squarefree, neither $q$ nor $q'$ divides $N$, $q' \neq q$, both $q \ge 5$ and $q' \ge 5$, and $D$ is a natural number with $2Nqq' \mid D$.
--
--   **The place over $q$.** $A_2$ is a valuation subring of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ with `hA₂ : A₂.LiesOverPrime q`, i.e. $q$ is a non-unit of $A_2$; it is assumed (as a `Fact`) that $A_2$ satisfies `DecompositionIsometric ℚ`, that is, every element of the decomposition subgroup of $A_2$ over $\mathbb{Q}$ preserves the valuation of $A_2$. Furthermore $v_2$ is a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ with $q \in v_2$.
--
--   **The definite side.** $a_1, b_1 \in \mathbb{Q}$ satisfy `IsDefiniteRamifiedExactlyAt q'`: $a_1 < 0$, $b_1 < 0$, and for a finite place $v$ of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a_1,b_1] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra (every non-zero element is a unit) exactly when $q' \in v$. Inside $B_1 = \mathbb{H}[\mathbb{Q},a_1,b_1]$, $\Lambda_1$ is a maximal order (an order maximal among the orders containing it) and $R_1 \le \Lambda_1$ is an Eichler order of level $N$, i.e. an intersection of two maximal orders whose relative index in the first is $N$. The unit $n_1$ of $B_1 \otimes_{\mathbb{Q}} \mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ lies in `primeHeckeSet R₁ q`, the set of adelic units $h$ with $h$ in the adelic box of $R_1$, with $q\,h^{-1}$ in that box, with $h^{-1}$ outside it and with $q^{-1}h$ outside it. The hypotheses on the associated order $\mathrm{meetOrder}\,R_1\,n_1 = R_1 \cap n_1 R_1 n_1^{-1}$ are: it is an Eichler order of level $Nq$ (`hS₁`); it is stable under conjugation by $n_1$ (`hnorm₁`); and shifting twice by $n_1$ is the identity on the class set of its adelic stabiliser (`hsq₁`). The class sets of the stabilisers of $\mathrm{meetOrder}\,R_1\,n_1$ and of $R_1$ are finite. Finally `hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁` asserts four things: the edge Hecke matrices (indexed by primes $\ell$, taken with the $u$-Hecke set at $\ell = q$, the level Hecke set for $\ell \mid N$ and the prime Hecke set otherwise) pairwise commute; the vertex Hecke matrices pairwise commute; for $\ell \neq q$ and each of the two degeneracy indices the joint degeneracy map carries the edge Hecke operator to the vertex Hecke operator; and the joint kernel of the two degeneracy maps is stable under every edge Hecke operator.
--
--   **The indefinite side.** $a, b \in \mathbb{Q}$ satisfy `IsIndefiniteRamifiedExactlyAt a b q q'`: $0 < a$ or $0 < b$, and $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ lies over $q$ or over $q'$; $\Lambda$ is a maximal order in $\mathbb{H}[\mathbb{Q},a,b]$.
--
--   **The rigid moduli package over $\mathbb{Z}[1/D]$.** $\bar F$ is a field over $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ which `IsCurveOver` that base (principal divisors exist, every place has residue field finite over the base, and $\Omega_{\bar F/\bar{\mathbb{Q}}}$ is free of rank one) and is essentially of finite type over it. $\pi_X : X \to \operatorname{Spec}(\mathbb{Z}[1/D])$ is a scheme over the localisation of $\mathbb{Z}$ away from $D$, $\bar s$ is a $\bar{\mathbb{Q}}$-point of that base, and $\mathrm{pt}$ assigns, to every commutative ring $S$, every base point $s$ over $\operatorname{Spec}(\mathbb{Z}[1/D])$ and every fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ structure, a section of $\pi_X$ over $s$. The package is required to be rigid: `pt_iso` says $\mathrm{pt}$ is constant on isomorphism classes; `pt_pullback` says that if $\varphi : S \to S'$ is compatible with the base points and $E'$ is a pullback of $E$ along $\varphi$ then $\mathrm{pt}(E')$ is $\operatorname{Spec}\varphi$ followed by $\mathrm{pt}(E)$; `pt_surjective` and `pt_injective` say that over an algebraically closed field $k$ the map $\mathrm{pt}$ is onto the sections of $\pi_X$ over $s$ and injective up to isomorphism of fake elliptic curves. Moreover $\mathfrak{M}$ is a `CurveModel` of $\bar F$ over $\bar{\mathbb{Q}}$ (an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\bar{\mathbb{Q}}$, with function field identified with $\bar F$ over the base and with closed points in bijection with the places of $\bar F$, the stalks matching the corresponding valuation subrings, and every finite set of points contained in an affine open), $e_{\mathfrak M} : \mathfrak{M}.C \to X \times_{\operatorname{Spec}\mathbb{Z}[1/D]} \operatorname{Spec}\bar{\mathbb{Q}}$ is an isomorphism with $e_{\mathfrak M}$ followed by the second projection equal to $\mathfrak{M}.\mathrm{toBase}$, and $\mathrm{gal}$ is a homomorphism from $\mathrm{Aut}_{\mathbb{Q}}(\bar{\mathbb{Q}})$ to the semilinear automorphisms of $\bar F$ over $\bar{\mathbb{Q}}$.
--
--   **The tower and its witness.** $\mathbb{T}$ is `HeckeTower.TowerData q q' Fbar`: for each prime $\ell \notin \{q,q'\}$ a field $\mathbb{T}.F\,\ell$ which is a curve over $\bar{\mathbb{Q}}$ and essentially of finite type, together with, for each arrow of the tower, a $\bar{\mathbb{Q}}$-algebra map $\bar F \to \mathbb{T}.F\,\ell$ that is finite and integral. For each such $\ell$, $\mathrm{galT}\,\ell$ is a semilinear Galois action on $\mathbb{T}.F\,\ell$, and $W$, $WT\,\ell$ are pairs (indexed by `Fin 2`) of semilinear automorphisms of $\bar F$, resp. of $\mathbb{T}.F\,\ell$. The structure $\mathrm{tw} : \mathrm{ModuliTowerWitnessD}\ \Lambda\ N\ q\ q'\ D\ \bar F\ X\ \pi_X\ \bar s\ \mathrm{pt}\ \mathfrak{M}\ e_{\mathfrak M}\ \mathrm{gal}\ \mathbb{T}\ \mathrm{galT}\ W\ WT$ records the moduli interpretation of the tower (its fields are summarised here): a fake elliptic curve $\mathrm{rep}\,P$ over $\bar{\mathbb{Q}}$ attached to every place $P$ of $\bar F$, whose point $\mathrm{pt}(\mathrm{rep}\,P)$ is the point of $X$ obtained from $P$ through $\mathfrak{M}.\mathrm{pointEquivPlace}$, $e_{\mathfrak M}$ and the first projection; representatives $\mathrm{repT}\,\ell$ of the places of $\mathbb{T}.F\,\ell$ by fake elliptic curves with extra level-$\ell$ structure, surjective and injective up to isomorphism of such objects; the statements that the base automorphism underlying $\mathrm{gal}\,\sigma$ and $\mathrm{galT}\,\ell\,\sigma$ is $\sigma$ itself while the base automorphisms underlying $W\,i$ and $WT\,\ell\,i$ are trivial; the compatibility of $\mathrm{repT}$ with restriction along the degeneracy arrows of the tower; and the remaining fields of the structure.
--
--   **The Mumford-side local data at $A_2$.** $\iota_2 : B_1 \to M_2(\mathrm{ratClosure}\,A_2)$ is an injective $\mathbb{Q}$-algebra map into the $2 \times 2$ matrices over the topological closure of the prime subfield inside the completion of $A_2$, $\rho_2 : B_1^{\times} \to \mathrm{PGL}(2, \mathrm{ratClosure}\,A_2)$ is a homomorphism, and $\mathrm{h}\rho_2$ says that $\rho_2$ is the projectivisation of $\iota_2$ on units. $\varpi_2$ is a pseudo-uniformiser of $\mathrm{ratClosure}\,A_2$ in the completion of $A_2$ whose image in the completion is $q$, and the holomorphic ring $\mathrm{HolRingOf}\,\varpi_2\,\rho_2$ is a domain.
--
--   **Frames.** $s_2$ assigns to each prime $\ell \notin \{q,q'\}$ a unit of $B_1$ and $\mathrm{sf}_2$ an adelic unit, subject to `hs₂`: at every finite place $u$ not over $q$ the component of $\mathrm{sf}_2\,\ell$ is $s_2\,\ell \otimes 1$; at every place over $q$ it is $1$; the product of the diagonal image of $\ell$ with $(\mathrm{sf}_2\,\ell)^{-1}$ lies in the level Hecke set $\mathrm{levelHeckeUSet}\,\Lambda_1\,(\mathrm{meetOrder}\,R_1\,n_1)\,\ell$ if $\ell \mid N$ and in $\mathrm{primeHeckeSet}\,(\mathrm{meetOrder}\,R_1\,n_1)\,\ell$ otherwise; and $\mathrm{nrd}(s_2\,\ell) = \ell$.
--
--   **The discrete groups.** $\Gamma_2$ assigns a subgroup of $B_1^{\times}$ to each object of the tower, with $\Gamma_2(\mathrm{none})$ consisting exactly of those units that lie, at every finite place $w \neq v_2$, in the subgroup generated by the local box units of $R_1$ at $w$, and whose reduced norm has even $q$-adic valuation; and $\Gamma_2(\mathrm{some}\,\ell) = \Gamma_2(\mathrm{none}) \cap s_2(\ell)\,\Gamma_2(\mathrm{none})\,s_2(\ell)^{-1}$.
--
--   **The interchange elements.** $w_2$ and $\bar w_2$ assign units of $B_1$ to the objects of the tower. By `hw₂`, $w_2(\mathrm{none})$ lies away from $v_2$ in the local box units of $R_1$ and has reduced norm $q$, and for each $\ell$ the element $w_2(\mathrm{some}\,\ell)$ has the same property for $\mathrm{meetOrder}\,R_1\,(\mathrm{sf}_2\,\ell)$ and reduced norm $q$. By `hwbar₂`, $\bar w_2(\mathrm{none})$ has reduced norm $q'$, lies in the local box units of $R_1$ at every place $u \neq v_2$ not containing $q'$, and conjugation by it preserves, at every $u \neq v_2$, both the local box of $R_1$ and the local box of $\Lambda_1$ (membership is equivalent before and after conjugation); the same conditions are imposed for each $\ell$ with $R_1$ replaced by $\mathrm{meetOrder}\,R_1\,(\mathrm{sf}_2\,\ell)$.
--
--   **The decomposition action.** $\mathrm{dIso}_2$ is a homomorphism from the decomposition subgroup of $A_2$ over $\mathbb{Q}$ to the isometric automorphisms of the completion of $A_2$ over $\mathrm{ratClosure}\,A_2$, and $\mathrm{hdIso}_2$ says that the ring equivalence underlying $\mathrm{dIso}_2\,\tau$ is the action of $\tau$ on the completion.
--
--   **Conclusion.** Under these hypotheses there exist a homomorphism $\chi_2$ from the decomposition subgroup of $A_2$ over $\mathbb{Q}$ to $\mathrm{Multiplicative}(\mathbb{Z}/2)$ and, for every object $j$ of the tower (the base object and each prime $\ell \notin \{q,q'\}$), a ring homomorphism $\iota M_2\,j$ from $\mathbb{T}.\mathrm{objField}\,j$ into the fraction field of $\mathrm{HolRingOf}\,\varpi_2\,\rho_2$, such that
--   $$\mathrm{DescentIntertwiningBase}\ q\ 0\ 1\ A_2\ \rho_2\ \varpi_2\ \Gamma_2\ w_2\ \bar w_2\ s_2\ \mathrm{dIso}_2\ \bar F\ \mathbb{T}\ \mathrm{gal}|_{D}\ (\mathrm{galT}\,\ell)|_{D}\ W\ WT\ \chi_2\ \iota M_2$$
--   holds, where the Galois actions are restricted to the decomposition subgroup along its inclusion into $\mathrm{Aut}_{\mathbb{Q}}(\bar{\mathbb{Q}})$, the residue parameter is $r = q$, and the two degeneracy indices are $0$ and $1$ in `Fin 2`. The predicate `DescentIntertwiningBase` is a conjunction of conditions on the pair $(\chi_2, \iota M_2)$: $\chi_2$ is trivial on the inertia subgroup of $A_2$ over $\mathbb{Q}$; $\chi_2$ is non-trivial on every element that is a Frobenius at $q$ for $A_2$; $\chi_2\,\tau = 1$ if and only if $\tau$ fixes every element $x$ of the residue field of $A_2$ with $x^{q^2} = x$; $\iota M_2$ at the base object carries the image of $z \in \bar{\mathbb{Q}}$ in $\bar F$ to the image of $z$ in the fraction field via the completion of $A_2$; the subfield generated by the image of the completion together with the image of $\iota M_2(\mathrm{none})$ is the invariant field of $\Gamma_2(\mathrm{none})$ acting on $\mathrm{HolRingOf}\,\varpi_2\,\rho_2$; $\iota M_2(\mathrm{none})$ carries finite families linearly independent over $\bar{\mathbb{Q}}$ to families linearly independent over the completion; and the further clauses of the definition, which relate the semilinear actions $\mathrm{gal}$, $\mathrm{galT}$, $W$ and $WT$ on the levels of the tower to $\chi_2$, the elements $w_2$, $\bar w_2$, $s_2$ and the embeddings $\iota M_2$.
--
--   This is the Čerednik–Drinfeld interchange at the place over $q$, in the form of a descent datum at the base level of the Hecke tower together with the embeddings of the tower's function fields into the Mumford-type holomorphic fraction field, obtained from a moduli-theoretic tower witness for fake elliptic curves with $\Lambda$-action and level-$N$ structure over $\mathbb{Z}[1/D]$. It is the version of the statement whose input is the rigid coarse-moduli package rather than an abstract tower with its Hecke laws, and it feeds the corresponding result formulated for a rigid oriented moduli witness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_descentIntertwiningBase_of_moduliTowerWitness_zero_one_of_two_mul_dvd.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve
open AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_zero_one_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)

    {a₁ b₁ : ℚ} (hdef₁ : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ q)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * q))
    (hnorm₁ : Submodule.conjByFiniteIdele (meetOrder R₁ n₁) n₁ = meetOrder R₁ n₁)
    (hsq₁ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)),
      classSetShift _ n₁ (classSetShift _ n₁ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    (hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁)

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

    [hiso₂ : Fact (A₂.DecompositionIsometric ℚ)]
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((q : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)

    (ι₂ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) (hι₂ : Function.Injective ι₂)
    (ρ₂ : (ℍ[ℚ, a₁, b₁])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₂)))
    (hρ₂ : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, ρ₂ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) x))

    (ϖ₂ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hϖ₂ : algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion ϖ₂.ϖ = ((q : AlgebraicClosure ℚ) : A₂.valuation.Completion))
    [hdom₂ : IsDomain (Omega.HolRingOf ϖ₂ ρ₂)]

    (s₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₂ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₂ ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₂ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₂ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ₂0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ₂ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (hΓ₂ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₂ (some ℓ) = Γ₂ none ⊓ (Γ₂ none).map (MulAut.conj (s₂ ℓ)).toMonoidHom)

    (w₂ wbar₂ : HeckeTower.Obj q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (hw₂ : (w₂ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ nrd (w₂ none : ℍ[ℚ, a₁, b₁]) = (q : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂ ∧ nrd (w₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q : ℚ))
    (hwbar₂ :
      (nrd (wbar₂ none : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₂ none) ∈ Submodule.localBoxUnits R₁ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox R₁ u ↔
            x ∈ Submodule.localBox R₁ u) ∧
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
            x ∈ Submodule.localBox Λ₁ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₂ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₁ (sf₂ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
              x ∈ Submodule.localBox Λ₁ u))))

    (dIso₂ : ↥(A₂.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hdIso₂ : ∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (x : A₂.valuation.Completion), (dIso₂ τ).toRingEquiv x = τ • x)
    :
    (∃ (χ₂ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (ιM₂ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂)),
        CerednikDrinfeld.DescentIntertwiningBase q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
          Fbar 𝕋 (gal.comp (A₂.decompositionSubgroup ℚ).subtype)
          (fun ℓ => (galT ℓ).comp (A₂.decompositionSubgroup ℚ).subtype) W WT χ₂ ιM₂) := by sorry
