-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq
-- name    : CerednikDrinfeld.QM.IsFineModuli.natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/43f3b9a8-241a-5339-9632-7305859c0196
-- title:
--   Stabiliser index count for extra levels at a fine moduli point
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders, natural numbers $N,m$, and a commutative ring $\mathcal{O}$ in which $m$ is invertible. Let $\pi_M\colon M\to\operatorname{Spec}\mathcal{O}$ together with the assignment $\mathrm{ptF}$, sending a fake elliptic curve with full level $m$ structure over an $\mathcal{O}$-scheme to a point of $M$, satisfy `IsFineModuli`: $\mathrm{ptF}$ is constant on isomorphism classes, compatible with base change, surjective on points, and injective up to isomorphism. Let $G$ be a finite group with $\rho\colon G\to\operatorname{Aut}M$ and labelling $\chi\colon G\to\Lambda$ satisfying `IsLevelTwistAction`: each $\rho(g)$ lies over the base, $\mathrm{ptF}$ of a twist by $\chi(g)$ equals $\mathrm{ptF}$ followed by $\rho(g)$, and $\chi$ is multiplicative, injective and surjective modulo $m\Lambda$. Let $\ell$ be a prime dividing $m$, and $L_0\subseteq\Lambda$ a submodule with $\ell\Lambda\subseteq L_0\subseteq\Lambda$, stable under left multiplication by $\Lambda$, and of additive relative index $\ell^2$ in $\Lambda$; let $H\le G$ consist exactly of those $g$ for which right multiplication by $\chi(g)$ preserves $L_0$. Let $k$ be an algebraically closed field with a structure morphism $s\colon\operatorname{Spec}k\to\operatorname{Spec}\mathcal{O}$, and $u=(E,P)$ a fake elliptic curve over $k$ with full level $m$ structure. Let $K\colon\mathrm{Fin}\,n\to$ the extra level structures of $E$ at $\ell$ be a family which is injective, and exhaustive, for the equivalence identifying two extra levels when exactly the same points of $E$ over $\operatorname{Spec}k$ factor through them. Let $i_0$ be an index such that for every algebraically closed field $k'$, every ring map $k\to k'$, and every point $Q$ of $E$ over the resulting geometric point, $Q$ factors through $(K\,i_0)$ precisely when $Q=x\cdot\bigl((m/\ell)P\bigr)$ for some $x\in\Lambda$ lying in $L_0$, where $x$ acts through `act` and $(m/\ell)P$ is the $(m/\ell)$-fold multiple of the level generator specialised to $k'$. Then the number of indices $i$ for which the pairs $(E,K\,i)$ and $(E,K\,i_0)$ are isomorphic (an isomorphism of the underlying schemes over $k$ respecting the group law, the $\Lambda$-action, the level $N$ structure and the extra level), multiplied by the number of $g\in H$ fixing $\mathrm{ptF}(u)$ in the sense that $\mathrm{ptF}(u)$ followed by $\rho(g)$ equals $\mathrm{ptF}(u)$, equals the number of all $g\in G$ fixing $\mathrm{ptF}(u)$ in that sense.
--
--   This is the orbit–stabiliser bookkeeping that compares, at a geometric point of the fine moduli scheme of fake elliptic curves with full level $m$ structure, the automorphisms of the point inside the level-twisting group $G$ with those preserving a chosen $\Lambda$-line $L_0$ modulo $\ell$: the index of the stabiliser intersected with $H$ counts the extra level structures at $\ell$ isomorphic to the one cut out by $L_0$. It is used in the construction of the moduli tower at level $\ell$ over the quaternionic moduli scheme, where stabiliser cardinalities must be matched before passing to quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.natCard_iso_extraLevel_mul_natCard_stabilizer_inf_eq
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
    {𝒪 : Type} [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))

    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀)

    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (n : ℕ) (K : Fin n → u.1.ExtraLevel ℓ)
    (hKdist : ∀ i j : Fin n,
      (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f,
        FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j)
    (hKexh : ∀ K' : u.1.ExtraLevel ℓ, ∃ i : Fin n,
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.1.f,
        FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x)

    (i₀ : Fin n)
    (hK₀ : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) u.1.f),
      FactorsThrough (K i₀).levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
          pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k' sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k' sk)) = Q) :
    Nat.card {i : Fin n // FakeEllipticCurve.WithExtraLevel.Iso
        (⟨u.1, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) ⟨u.1, K i₀⟩} *
      Nat.card {g : G // g ∈ H ∧ (ptF k s u).1 ≫ (ρ g).hom = (ptF k s u).1} =
    Nat.card {g : G // (ptF k s u).1 ≫ (ρ g).hom = (ptF k s u).1} := by sorry
