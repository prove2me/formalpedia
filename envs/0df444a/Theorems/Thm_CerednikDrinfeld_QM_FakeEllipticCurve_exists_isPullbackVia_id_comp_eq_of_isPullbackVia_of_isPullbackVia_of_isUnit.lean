-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/2a0a40b8-eece-55a8-9a30-be43a1bc8aa2
-- title:
--   Comparison of two pull-backs of a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, commutative rings $S'$ and $S$, and a ring homomorphism $\rho : S' \to S$ such that the image of $N$ in $S$ is a unit. Let $E$ be a fake elliptic curve over $S'$ for the data $(\Lambda,N)$, and let $E_1$, $E_2$ be fake elliptic curves over $S$, each equipped with a morphism of schemes $g_i : E_i.A \to E.A$ satisfying `IsPullbackVia` $\rho$, that is: the square formed by $g_i$, the structure morphism $E_i.f$, the structure morphism $E.f$ and $\operatorname{Spec}(\rho)$ is cartesian; for every scheme $T$, every $t' : T \to \operatorname{Spec} S$ and all $T$-points $P,Q$ of $E_i.A$ over $t'$, composing the relative-group-law product of $P$ and $Q$ with $g_i$ agrees with the product in $E$ of $P \circ g_i$ and $Q \circ g_i$ over $t'$ followed by $\operatorname{Spec}(\rho)$; for each $x \in \Lambda$ the action morphisms satisfy $g_i \circ E_i.\mathrm{act}(x) = E.\mathrm{act}(x) \circ g_i$; and every point of $E_i.A$ factoring through $E_i.\mathrm{lev}$ has its composite with $g_i$ factoring through $E.\mathrm{lev}$. The conclusion asserts the existence of a morphism $h : E_2.A \to E_1.A$ with $g_1 \circ h = g_2$ and $E_1.f \circ h = E_2.f$, which satisfies `IsPullbackVia` for the identity of $S$: the square $h$, $E_2.f$, $E_1.f$, $\operatorname{Spec}(\mathrm{id}_S)$ is cartesian, $h$ is compatible with the relative group laws on $T$-points, commutes with the $\Lambda$-actions, and carries points factoring through $E_2.\mathrm{lev}$ to points whose composite with $h$ factors through $E_1.\mathrm{lev}$.
--
--   This is the uniqueness, up to canonical isomorphism, of a base change of a fake elliptic curve with $\Lambda$-action and level-$N$ structure: two realisations of $E \times_{\operatorname{Spec} S'} \operatorname{Spec} S$ are identified by a morphism which is itself a base change along the identity, hence an isomorphism respecting all the moduli data. It is used throughout the rigidification arguments for the Čerednik–Drinfeld moduli problem, where pull-backs constructed by different routes must be compared; the level clause is obtained from the étaleness of the level structure when $N$ is invertible, via [`CerednikDrinfeld.QM.FakeEllipticCurve.etale_lev_and_forall_factorsThrough_iff_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.etale_lev_and_forall_factorsThrough_iff_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S' S : Type} [CommRing S'] [CommRing S] (ρ : S' →+* S) (hN : IsUnit ((N : ℕ) : S))
    (E : FakeEllipticCurve Λ N S')
    (E₁ : FakeEllipticCurve Λ N S) (g₁ : E₁.A ⟶ E.A) (h₁ : FakeEllipticCurve.IsPullbackVia ρ E E₁ g₁)
    (E₂ : FakeEllipticCurve Λ N S) (g₂ : E₂.A ⟶ E.A) (h₂ : FakeEllipticCurve.IsPullbackVia ρ E E₂ g₂) :
    ∃ h : E₂.A ⟶ E₁.A, h ≫ g₁ = g₂ ∧ h ≫ E₁.f = E₂.f ∧ FakeEllipticCurve.IsPullbackVia (RingHom.id S) E₁ E₂ h := by sorry
