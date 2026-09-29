-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_fstHom_forall_existsUnique_smul_of_level_one_of_isAlgClosed_of_charP
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_fstHom_forall_existsUnique_smul_of_level_one_of_isAlgClosed_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/5f610790-f329-55ae-9b80-140ea3f5967e
-- title:
--   First-order deformations of a fake elliptic curve form a line
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'` (namely $a>0$ or $b>0$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$), and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders. Let $k$ be an algebraically closed field of characteristic a prime $\ell$ in which the image of $qq'$ is a unit, and let $u$ be a fake elliptic curve of level $1$ over $k$ (an abelian surface $u.A\to\operatorname{Spec}k$ with commutative relative group law, $\Lambda$-action and level data). Throughout, `IsPullbackVia` $\varphi$ $E$ $E'$ $g$ means that $g:E'.A\to E.A$ makes a pullback square over $\operatorname{Spec}\varphi$, is compatible with the relative group laws, intertwines the $\Lambda$-actions, and carries points factoring through $E'.\mathrm{lev}$ to points factoring through $E.\mathrm{lev}$. The assertion: there are a fake elliptic curve $v$ of level $1$ over the dual numbers $k[\varepsilon]$ and a map $g_v:u.A\to v.A$ exhibiting $u$ as the pullback of $v$ along $\varepsilon\mapsto 0$, such that for every pair $(t,g_t)$ of the same kind: (i) there is $c\in k$ with the property that every $(w,g_w)$ of the same kind which is the pullback of $v$ along $\varepsilon\mapsto c\varepsilon$ via some $h_w:w.A\to v.A$ with $g_w$ followed by $h_w$ equal to $g_v$ admits a map $h:t.A\to w.A$ which is a pullback over the identity of $k[\varepsilon]$ with $g_t$ followed by $h$ equal to $g_w$; and (ii) such a $c$ is unique, in the sense that if $c,c'$ and $(w,g_w,h_w)$, $(w',g_{w'},h_{w'})$ are two such configurations (for $\varepsilon\mapsto c\varepsilon$ and $\varepsilon\mapsto c'\varepsilon$ respectively) and $t$ admits such maps to both $w$ and $w'$, then $c=c'$.
--
--   This is the computation of the tangent space to the deformation functor of a rigidified level-one fake elliptic curve at a residue characteristic not dividing the discriminant $qq'$: first-order deformations, rigidified by the comparison map to $u$, are exhausted without repetition by the pullbacks of one deformation $v$ along the scalings $\varepsilon\mapsto c\varepsilon$, so the deformation space is a line. It feeds the construction and uniqueness of power-series towers of deformations used for the formal neighbourhoods in the Čerednik–Drinfeld description of integral models of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_fstHom_forall_existsUnique_smul_of_level_one_of_isAlgClosed_of_charP.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_fstHom_forall_existsUnique_smul_of_level_one_of_isAlgClosed_of_charP
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (hqq'u : IsUnit ((q * q' : ℕ) : k))
    (u : FakeEllipticCurve Λ 1 k) :
    ∃ (v : FakeEllipticCurve Λ 1 (DualNumber k)) (gv : u.A ⟶ v.A)
      (_ : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom v u gv),
      ∀ (t : FakeEllipticCurve Λ 1 (DualNumber k)) (gt : u.A ⟶ t.A),
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
          c = c') := by sorry
