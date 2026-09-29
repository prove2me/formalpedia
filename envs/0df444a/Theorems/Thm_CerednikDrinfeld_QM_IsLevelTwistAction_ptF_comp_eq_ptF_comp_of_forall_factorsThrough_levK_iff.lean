-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsLevelTwistAction_ptF_comp_eq_ptF_comp_of_forall_factorsThrough_levK_iff
-- name    : CerednikDrinfeld.QM.IsLevelTwistAction.ptF_comp_eq_ptF_comp_of_forall_factorsThrough_levK_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/73448be2-b554-5294-91bc-68d7c61e030f
-- title:
--   Level structures cutting out the same L₀-line agree over X_H
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is an order (contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$, and is finitely generated), natural numbers $N,m$, and a commutative ring $\mathcal{O}$ in which the image of $m$ is a unit. Let $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$ together with an assignment $\mathrm{ptF}$ sending each commutative ring $S$, each morphism $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$ and each pair consisting of a fake elliptic curve $E$ over $S$ of level $N$ and a full level-$m$ structure on $E$ to a morphism $\operatorname{Spec}S\to M$ over $s$, and assume `IsFineModuli`: $\mathrm{ptF}$ is constant on isomorphism classes, compatible with base change along ring homomorphisms, surjective onto all such $M$-points, and injective up to isomorphism. Let $G$ be a group, $\rho:G\to\operatorname{Aut}M$ a homomorphism and $\chi:G\to\Lambda$ a labelling such that `IsLevelTwistAction` holds: each $\rho(g)$ is a morphism over $\pi_M$, twisting a level structure by $\chi(g)$ transforms its moduli point by $\rho(g)$, and $\chi$ is multiplicative, injective and surjective modulo $m\Lambda$. Let $\ell$ be a prime dividing $m$, let $L_0\subseteq\Lambda$ be a $\mathbb{Z}$-submodule with $\ell\Lambda\subseteq L_0$, and let $H\le G$ be a subgroup containing every $g\in G$ with $L_0\,\chi(g)\subseteq L_0$. Let $\pi_H:M\to X_H$ be a morphism with $\rho(h)$ followed by $\pi_H$ equal to $\pi_H$ for all $h\in H$. Finally let $S$ be a commutative ring, $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$, let $E$ be a fake elliptic curve over $S$ of level $N$, let $K$ be an extra level-$\ell$ structure on $E$ (a finite flat Λ-stable subgroup scheme $\mathrm{levK}:K\to E.A$ of rank $\ell^2$ killed by $\ell$ and disjoint from $E.\mathrm{lev}$), and let $P,P'$ be full level-$m$ structures on $E$. Assume that for every algebraically closed field $k$, every ring homomorphism $sk:S\to k$ and every point $Q$ of $E$ over the geometric point $\operatorname{Spec}k\to\operatorname{Spec}S$ determined by $sk$, $Q$ factors through $\mathrm{levK}$ if and only if $Q$ is the image of the $(m/\ell)$-fold multiple of the fibre of $P$ under the action of some $x\in\Lambda$ with $x\in L_0$; and assume the same description with $P'$ in place of $P$. Then the moduli point of $(E,P')$ followed by $\pi_H$ equals the moduli point of $(E,P)$ followed by $\pi_H$, as morphisms $\operatorname{Spec}S\to X_H$.
--
--   This is the descent step showing that the moduli point of a fake elliptic curve with full level-$m$ structure depends, after passing to a quotient on which the stabiliser subgroup $H$ acts trivially, only on the $\ell$-level subgroup $L_0\cdot\frac{m}{\ell}P$ cut out by the level structure; it is the analogue for a proper subgroup $H$ of the corresponding statement for all of $G$. It is used in the construction of a coarse moduli scheme for the quotient level structure attached to an indefinite quaternion algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsLevelTwistAction_ptF_comp_eq_ptF_comp_of_forall_factorsThrough_levK_iff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsLevelTwistAction.ptF_comp_eq_ptF_comp_of_forall_factorsThrough_levK_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛord : IsOrder Λ) {N m : ℕ} {𝒪 : Type} [CommRing 𝒪]
    (hm' : IsUnit ((m : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hG : IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (H : Subgroup G) (hH : ∀ g : G, (∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀) → g ∈ H)
    {XH : Scheme.{0}} (πH : M ⟶ XH) (hπH : ∀ h : H, (ρ h).hom ≫ πH = πH)
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (E : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ) (P P' : E.FullLevel m)
    (hP : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q)
    (hP' : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P'.P k sk)) = Q) :
    (ptF S s ⟨E, P'⟩).1 ≫ πH = (ptF S s ⟨E, P⟩).1 ≫ πH := by sorry
