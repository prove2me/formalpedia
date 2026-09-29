-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/7758676e-3250-5f6d-8349-58419fa6f258
-- title:
--   An open and closed disjointness locus on the fine moduli scheme
-- statement:
--   Let $q,q'$ be primes and $a,b\in\mathbb{Q}$ with $\mathbb{H}[\mathbb{Q},a,b]$ indefinite ($0<a$ or $0<b$) and ramified exactly at $q,q'$, in the sense that for a height-one prime $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible precisely when $v$ divides $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $N,m\in\mathbb{N}$, and let $\mathcal{O}$ be a commutative ring in which the images of $N$ and $m$ are units. Let $\pi_M\colon M\to\operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$ together with an assignment $\mathrm{ptF}$ sending each commutative ring $S$, each $s\colon\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$ and each pair $w=(E,P)$ consisting of a fake elliptic curve $E$ over $S$ with $\Lambda$-action and level-$N$ structure $\mathrm{lev}\colon C\to A$ and a full level-$m$ structure $P$, to a morphism $\operatorname{Spec}S\to M$ over $s$; assume `IsFineModuli`, i.e. $\mathrm{ptF}$ is constant on isomorphism classes, compatible with pullback along ring homomorphisms, surjective onto the points over $s$, and injective up to isomorphism. Let $G$ be a group, $\rho\colon G\to\operatorname{Aut}M$ and $\chi\colon G\to\Lambda$ satisfy `IsLevelTwistAction`: each $\rho(g)$ lies over $\pi_M$, $\mathrm{ptF}$ of a twist of $w$ by $\chi(g)$ is $\mathrm{ptF}(w)$ followed by $\rho(g)$, and $\chi$ is multiplicative, injective and surjective modulo $m$. Let $\ell$ be a prime dividing $m$ and let $L_0\subseteq\Lambda$ be a submodule with $\ell\Lambda\subseteq L_0$, stable under left multiplication by $\Lambda$, and of relative index $\ell^2$ in $\Lambda$ as additive subgroups. The conclusion asserts the existence of an open subscheme $V$ of $M$ whose underlying set is closed, such that: (a) for all $S$, $s$ and $w$ as above, the set-theoretic image of $\mathrm{ptF}(S,s,w)$ lies in $V$ if and only if for every algebraically closed field $k$, every ring homomorphism $sk\colon S\to k$ and every $x\in\Lambda$ with $x\in L_0$, the point $x\cdot\bigl((m/\ell)\,P\bigr)$ over the geometric point $\operatorname{Spec}k\to\operatorname{Spec}S$ induced by $sk$, if it factors through $\mathrm{lev}$ (i.e. lifts along $C\to A$), equals the identity section of the group law there; (b) for every $g\in G$ with $L_0\chi(g)\subseteq L_0$, the preimage of $V$ under $\rho(g)$ is $V$; and (c) if $\ell\nmid N$ then $V$ is all of $M$.
--
--   This is the globalisation over the fine moduli scheme $M$ of the chart-wise statement that, over an affine base, the locus where the $L_0$-line of $\ell$-torsion meets the level-$N$ structure trivially is open and closed; the resulting open-and-closed locus, together with its equivariance under the stabiliser of $L_0$ in the twisting group, feeds into the construction of the quotient coarse moduli scheme with extra level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsFineModuli.exists_opens_isClosed_range_subset_iff_forall_factorsThrough_lev_imp
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N m : ℕ} {𝒪 : Type} [CommRing 𝒪]
    (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hG : IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2) :
    ∃ V : M.Opens, IsClosed (V : Set ↥M) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S),
        Set.range (ptF S s w).1 ⊆ (V : Set ↥M) ↔
          ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (x : ↥Λ), (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough w.1.lev
          (pushPt (w.1.act x) (w.1.act_over x)
            (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk))) →
        pushPt (w.1.act x) (w.1.act_over x)
            (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = w.1.L.one (geomPoint k sk)) ∧
      (∀ g : G, (∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀) → (ρ g).hom ⁻¹ᵁ V = V) ∧
      (¬ ℓ ∣ N → V = ⊤) := by sorry
