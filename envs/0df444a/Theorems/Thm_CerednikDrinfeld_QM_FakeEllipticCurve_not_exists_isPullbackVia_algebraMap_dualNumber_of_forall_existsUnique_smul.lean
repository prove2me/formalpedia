-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/fb72fa4f-450d-52f6-bd91-0c98becbd13e
-- title:
--   Generators of the deformation tangent line are non-trivial
-- statement:
--   Fix primes $q \neq q'$ and rationals $a, b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for $\mathbb{H}[\mathbb{Q},a,b]$, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all non-zero elements invertible exactly when $q \in v$ or $q' \in v$; let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order and is maximal among orders, let $k$ be an algebraically closed field of characteristic $\ell$ in which $qq'$ is invertible. Let $u$ be a fake elliptic curve for $\Lambda$ of level $1$ over $k$, let $v$ be one over the dual numbers $k[\varepsilon]$, and let $gv : u.A \to v.A$ satisfy `FakeEllipticCurve.IsPullbackVia` for the first-projection ring map $k[\varepsilon] \to k$: the square formed by $gv$, the structure maps of $u$ and $v$ and $\operatorname{Spec}$ of that map is cartesian, $gv$ carries the relative group law of $u$ on $T$-points to that of $v$, intertwines the $\Lambda$-actions, and carries points factoring through the level map of $u$ to points factoring through that of $v$. Assume further that $v$ generates the tangent line in the following sense: for every $t$ over $k[\varepsilon]$ with $gt : u.A \to t.A$ cartesian in this sense over the first projection, there is a $c \in k$ such that every $w$ over $k[\varepsilon]$ with $gw$ cartesian over the first projection and with $hw : w.A \to v.A$ exhibiting $w$ as the pullback of $v$ along $\varepsilon \mapsto c\varepsilon$ (i.e. `IsPullbackVia` for `TrivSqZeroExt.map (c • LinearMap.id)`) and $gw$ followed by $hw$ equal to $gv$, receives a map $h$ from $t$ that is an isomorphism over the identity of $k[\varepsilon]$ in the sense of `IsPullbackVia` with $gt$ followed by $h$ equal to $gw$; and such a $c$ is unique, in that any two scalars $c, c'$ with associated data $(w, gw, hw)$, $(w', gw', hw')$ as above and with $t$ mapping compatibly to both $w$ and $w'$ must be equal. Finally let $w$ over $k[\varepsilon]$ with $gw : u.A \to w.A$ be cartesian over the first projection, and let $h : w.A \to v.A$ exhibit $v$ as a pullback of $w$ over the identity of $k[\varepsilon]$ with $gw$ followed by $h$ equal to $gv$. Then there is no $h_0 : w.A \to u.A$ satisfying `IsPullbackVia` for $k \to k[\varepsilon]$ (so exhibiting $w$ as the trivial deformation $u \times_{\operatorname{Spec} k} \operatorname{Spec} k[\varepsilon]$, compatibly with group law, $\Lambda$-action and level) with $gw$ followed by $h_0$ equal to the identity of $u.A$.
--
--   This is the non-triviality half of the description of the tangent space to the deformation functor of a level-one fake elliptic curve: a first-order deformation isomorphic to a generator $v$ of that tangent line cannot be the trivial deformation, pointed by its canonical section. It is used when assembling a tower of deformations over a complete discrete valuation ring whose first layer is non-trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (hqq'u : IsUnit ((q * q' : ℕ) : k))
    (u : FakeEllipticCurve Λ 1 k)
    (v : FakeEllipticCurve Λ 1 (DualNumber k)) (gv : u.A ⟶ v.A)
    (hv : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom v u gv)
    (hgen : ∀ (t : FakeEllipticCurve Λ 1 (DualNumber k)) (gt : u.A ⟶ t.A),
        FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom t u gt →
        (∃ c : k, ∀ (w : FakeEllipticCurve Λ 1 (DualNumber k)) (gw : u.A ⟶ w.A) (hw : w.A ⟶ v.A),
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v w hw →
          gw ≫ hw = gv →
          ∃ h : t.A ⟶ w.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w t h ∧ gt ≫ h = gw) ∧
        (∀ (c c' : k) (w w' : FakeEllipticCurve Λ 1 (DualNumber k)) (gw : u.A ⟶ w.A) (gw' : u.A ⟶ w'.A)
          (hw : w.A ⟶ v.A) (hw' : w'.A ⟶ v.A),
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v w hw →
          gw ≫ hw = gv →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w' u gw' →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) (c' • (LinearMap.id : k →ₗ[k] k))).toRingHom v w' hw' →
          gw' ≫ hw' = gv →
          (∃ h : t.A ⟶ w.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w t h ∧ gt ≫ h = gw) →
          (∃ h' : t.A ⟶ w'.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w' t h' ∧ gt ≫ h' = gw') →
          c = c'))
    (w : FakeEllipticCurve Λ 1 (DualNumber k)) (gw : u.A ⟶ w.A)
    (hw : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw)
    (h : w.A ⟶ v.A) (hh : FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) v w h) (hgwh : gw ≫ h = gv) :
    ¬ ∃ h₀ : w.A ⟶ u.A,
        FakeEllipticCurve.IsPullbackVia (algebraMap k (DualNumber k)) u w h₀ ∧ gw ≫ h₀ = 𝟙 u.A := by sorry
