-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_and_apply_nilEval_eq_of_isFormalModuleVia_of_isIso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_and_apply_nilEval_eq_of_isFormalModuleVia_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/b1d1bfc6-3a93-5971-a4c8-254fbfed1f7f
-- title:
--   Transporting formal coordinates along an isomorphism of formal mathcal O_D-modules
-- statement:
--   Let $a,b\in\mathbb Q$, let $\Lambda$ be a $\mathbb Z$-submodule of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, let $N$ be a natural number and $q$ a prime, and fix a map $\mathrm{coord}:\Lambda\to \mathrm{Zp2}\,q\times \mathrm{Zp2}\,q$ into pairs of Witt vectors over $\mathbb F_{q^2}$. Let $B$ be a commutative ring, $E$ a `FakeEllipticCurve Λ N B` (a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} B$, a commutative relative group law $E.L$, the property bundle, two-dimensional fibres, and an action $E.\mathrm{act}$ of $\Lambda$ by endomorphisms over $B$), and let $X,Y$ be formal $\mathcal O_D$-modules over $B$ for $q$, that is, two-dimensional commutative formal group laws $X.F$ equipped with a multiplicative and additive action of $\mathrm{Zp2}\,q$ by endomorphisms together with a uniformiser series $X.\varpi$ satisfying $\varpi\circ\varpi=\mathrm{act}(q)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\varphi(a))\circ\varpi$. Let $\theta$ assign, to each $B$-algebra $B'$ and each tuple in $(B')^2$, a section of $E.f$ over $\operatorname{Spec} B'$, and assume `E.IsFormalModuleVia coord X θ`: $\theta$ is a system of formal coordinates for $E.L$ with group law $X.F$ (natural in $B$-algebra maps, and for every ideal $J$ of a $B$-algebra $B'$ with $J^{n+1}=0$ restricting to a bijection from tuples with entries in $J$ onto the points infinitesimal along $J$ and carrying $X.F$'s truncated addition to $E.L.\mathrm{mul}$), and for each $m\in\Lambda$ it carries the series $X.\mathrm{act}((\mathrm{coord}\,m)_1)+_{X.F}X.\mathrm{act}((\mathrm{coord}\,m)_2)\circ X.\varpi$, evaluated by truncation at level $n$, to $E.\mathrm{act}(m)$. Let $u:X\to Y$ be a homomorphism of formal $\mathcal O_D$-modules admitting a two-sided inverse. Then there is a system $\theta'$ of formal coordinates with `E.IsFormalModuleVia coord Y θ'` such that for every $B$-algebra $B'$, every ideal $J$ of $B'$ and every $n$ with $J^{n+1}=0$, and every tuple $s$ with entries in $J$, one has $\theta'\bigl(\mathrm{nilEval}\,n\,(u.\mathrm{toSeries}\,i)\,s\bigr)_i=\theta(s)$.
--
--   This is the transport of the formal $\mathcal O_D$-module structure attached to a fake elliptic curve along an isomorphism of formal $\mathcal O_D$-modules: the new coordinates are $\theta$ composed with the inverse of $u$, so that $\theta'\circ u=\theta$ on tuples with nilpotent entries. It is used in the Čerednik–Drinfeld part of the development, where rigidified deformations and the Serre–Tate style dictionary for fake elliptic curves require the freedom to replace the formal module by any isomorphic one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_and_apply_nilEval_eq_of_isFormalModuleVia_of_isIso.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_and_apply_nilEval_eq_of_isFormalModuleVia_of_isIso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q)
    (B : Type) [CommRing B] (E : FakeEllipticCurve Λ N B) (X Y : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (u : FormalODModule.Hom X Y) (hu : u.IsIso) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates E.f 2, E.IsFormalModuleVia coord Y θ' ∧
      ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ' B' (fun i => MvFormalGroup.nilEval n (u.toSeries i) s) = θ B' s := by sorry
