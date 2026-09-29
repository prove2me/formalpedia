-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_frobeniusTwist_of_isLevelIsogeny_of_forall_factorsThrough_eq_one
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_frobeniusTwist_of_isLevelIsogeny_of_forall_factorsThrough_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/121b37ec-af78-567f-bcee-6363e4ea3fbd
-- title:
--   Level-ℓ quotient by a pointless extra level is the Frobenius twist
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $k$ be an algebraically closed field of characteristic a prime $\ell$ with $\ell \nmid N$, and assume $\Lambda$ is a maximal order, i.e. an order that contains no order properly ([`QuaternionAlgebra.IsMaximalOrder`](def/QuaternionAlgebra_EichlerOrder.html#L63)). Let $q,q'$ be primes such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$; assume $\ell \neq q$ and $\ell \neq q'$. Let $E,E_\ell$ be fake elliptic curves over $k$ with $\Lambda$-action and level-$N$ structure, equipped with a Frobenius–Verschiebung datum $D$ for $\ell$: a morphism $\mathrm{pr} : E_\ell.A \to E.A$ exhibiting $E_\ell$ as the base change of $E$ along the $\ell$-power Frobenius of $k$ and compatible with the group laws, the $\Lambda$-actions and the level structures, together with morphisms $F : E.A \to E_\ell.A$ and $V : E_\ell.A \to E.A$ over $k$ that are homomorphisms for the relative group laws, commute with the $\Lambda$-actions and preserve the level-$N$ structures. Let $K$ be an extra level structure on $E$ at $\ell$: a closed immersion $\mathrm{lev}_K : K \to E.A$ whose points form a subgroup of $E$ killed by $\ell$, stable under $\Lambda$, meeting the level-$N$ structure only in the identity, finite flat and locally of finite presentation over the base of rank $\ell^2$, with geometric fibres isomorphic as groups to $(\mathbb{Z}/\ell)^2$. Let $d$ be a fake elliptic curve over $k$ which is a level-$\ell$ isogeny quotient of $(E,K)$: there are morphisms $\varphi : E.A \to d.A$ and $\psi : d.A \to E.A$ over $k$, each a homomorphism for the relative group laws and commuting with the $\Lambda$-actions, whose two composites are the action of $\ell$ whenever $\ell \in \Lambda$, such that a point of $E$ is killed by $\varphi$ exactly when it factors through $\mathrm{lev}_K$, and such that $\varphi$ carries points factoring through the level-$N$ structure of $E$ to points factoring through that of $d$. Assume finally that every $k$-point of $E$ (section over $\mathrm{Spec}\,k$) factoring through $\mathrm{lev}_K$ is the identity section, i.e. $K(k) = 0$. Then $d$ and $E_\ell$ are isomorphic as fake elliptic curves: there is an isomorphism $d.A \cong E_\ell.A$ over $k$ compatible with the group laws, the $\Lambda$-actions, and the level-$N$ structures in both directions.
--
--   This is the inseparable half of the characteristic-$\ell$ dichotomy for fake elliptic curves: when the extra level at $\ell$ carries no nonzero rational point it is the kernel of Frobenius, so the corresponding level-$\ell$ quotient is the Frobenius twist $E^{(\ell)}$. Together with its separable counterpart it supplies the local input for the Eichler–Shimura congruence on the Shimura curve attached to the indefinite quaternion algebra of discriminant $qq'$, and it is used in the computation of the Frobenius action on the moduli description of that curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_frobeniusTwist_of_isLevelIsogeny_of_forall_factorsThrough_eq_one.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_frobeniusTwist_of_isLevelIsogeny_of_forall_factorsThrough_eq_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (K : E.ExtraLevel ℓ) (d : FakeEllipticCurve Λ N k)
    (hd : IsLevelIsogeny ℓ (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) d)

    (hK : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      FactorsThrough K.levK P → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    FakeEllipticCurve.Iso d Eℓ := by sorry
