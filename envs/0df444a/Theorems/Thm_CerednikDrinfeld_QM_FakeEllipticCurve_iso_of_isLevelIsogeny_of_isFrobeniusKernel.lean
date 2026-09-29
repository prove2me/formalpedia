-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_of_isFrobeniusKernel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_of_isFrobeniusKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/225f29ee-2f93-5036-988e-520146dcf194
-- title:
--   Quotient by the Frobenius kernel is the Frobenius twist
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $k$ be an algebraically closed field, $\ell$ a prime with $k$ of characteristic $\ell$, and assume $\ell \nmid N$ and that $\Lambda$ is an order, i.e. $\Lambda$ contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$ and is finitely generated. Let $E$ and $E_\ell$ be fake elliptic curves over $k$ of level $N$ (abelian schemes of relative dimension $2$ with a commutative relative group law, an action of $\Lambda$ subject to the trace condition, and a level structure $\mathrm{lev}$), and let $D$ be a Frobenius–Verschiebung datum for $(\ell, E, E_\ell)$: a morphism $\mathrm{pr}\colon E_\ell \to E$ exhibiting $E_\ell$ as the base change of $E$ along the $\ell$-power Frobenius of $k$, compatible with the group laws, the $\Lambda$-actions and the level structures, together with morphisms $F\colon E \to E_\ell$ and $V\colon E_\ell \to E$ over $k$ that are homomorphisms for the relative group laws, commute with the $\Lambda$-actions and preserve the level structures. Let $K$ be an extra level structure at $\ell$ on $E$: a closed immersion $\mathrm{lev}K\colon K \to E$ whose sections form a subgroup of the relative group law, killed by $\ell$, stable under $\Lambda$, meeting the level-$N$ structure only in the identity, finite flat of finite presentation of rank $\ell^2$ on every fibre, with geometric fibres isomorphic to $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$. Assume the predicate `IsFrobeniusKernel` for $(\langle E, K\rangle, D)$: for every scheme $T$ over $\operatorname{Spec} k$ and every section $P$ of $E$ over $T$, $P$ factors through $\mathrm{lev}K$ exactly when $F \circ P$ is the identity section of $E_\ell$. Finally let $d$ be a fake elliptic curve over $k$ of level $N$ and assume $d$ is a level-$\ell$ isogeny quotient of $(E,K)$: there are morphisms $\varphi\colon E \to d$ and $\psi\colon d \to E$ over $k$, both homomorphisms for the group laws and $\Lambda$-equivariant, with $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$ equal to the action of $\ell$ whenever $\ell \in \Lambda$, such that a section $P$ of $E$ is killed by $\varphi$ exactly when it factors through $\mathrm{lev}K$, and $\varphi$ carries sections factoring through $E.\mathrm{lev}$ to sections factoring through $d.\mathrm{lev}$. Then $d$ and $E_\ell$ are isomorphic as fake elliptic curves of level $N$: there is an isomorphism of schemes $d \cong E_\ell$ over $\operatorname{Spec} k$ compatible with the relative group laws, commuting with the $\Lambda$-actions, and matching the level-$N$ structures in both directions.
--
--   This is the statement that the quotient of a fake elliptic curve by the kernel of its relative Frobenius is the Frobenius twist, $E/\ker F \cong E^{(\ell)}$, formulated as uniqueness of the level-$\ell$ isogeny quotient in the inseparable case. It is used in the analysis of the special fibre at $\ell$ of the quaternionic moduli problem, where the dichotomy between inseparable and separable level-$\ell$ isogenies underlies the Eichler–Shimura congruence; it is cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_isLevelIsogeny_of_exists_factorsThrough_ne_one`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_isLevelIsogeny_of_exists_factorsThrough_ne_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_of_isFrobeniusKernel.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_of_isFrobeniusKernel
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsOrder Λ)
    (E Eℓ : FakeEllipticCurve Λ N k) (D : FrobeniusVerschiebungData ℓ E Eℓ)
    (K : E.ExtraLevel ℓ) (hK : IsFrobeniusKernel (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) D)
    (d : FakeEllipticCurve Λ N k) (hd : IsLevelIsogeny ℓ (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) d) :
    FakeEllipticCurve.Iso d Eℓ := by sorry
