-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/10eae545-0499-573d-9bf3-8dae25b54fa1
-- title:
--   Level subgroups of the theta group give translation cocycles
-- statement:
--   Let $k$ be a field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, let $L$ be a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$), let $hc$ witness that $L$ is commutative, and let $M$ be an $\mathcal O_A$-module. Write $L.\mathrm{AlgPoints}\,hc\,k$ for the group of $k$-points of $f$ written additively, and for such a point $P$ write $T_P = \mathtt{translation}\,f\,L\,P$ for the endomorphism of $A$ obtained by multiplying the identity point by the constant point $P$. The group $\mathtt{thetaGroup}\,f\,L\,hc\,M$ is the subgroup of $\operatorname{Aut}(A, M) \times (L.\mathrm{AlgPoints}\,hc\,k)^{\times}$ of pairs whose automorphism of the pair has base morphism equal to translation by the second component, and $\mathtt{pt}$ is its projection to the point. Let $n \in \mathbb N$ and let $K$ be a subgroup of this theta group such that $\mathtt{pt}$ is injective on $K$ (any two elements of $K$ with the same point agree) and such that a point $Q$ lies in $\mathtt{pt}(K)$ exactly when $n \cdot Q = 0$. The conclusion asserts the existence of a family $\psi$ assigning to every $k$-point $P$ with $n \cdot P = 0$ an isomorphism $\psi_P : M \cong T_P^{*} M$ of $\mathcal O_A$-modules such that: $\psi_0$ is the canonical isomorphism $M \cong \mathbf 1_A^{*} M$ followed by the inverse of the comparison isomorphism coming from $T_0 = \mathbf 1_A$; and for all $P, Q$ with $n \cdot P = 0$, $n \cdot Q = 0$ and $n \cdot (P + Q) = 0$, the isomorphism $\psi_{P+Q}$ equals $\psi_P$ followed by $T_P^{*}\psi_Q$, followed by the canonical isomorphism $T_P^{*} T_Q^{*} M \cong (T_P \text{ then } T_Q)^{*} M$, followed by the inverse of the comparison isomorphism coming from the identity $T_{P+Q} = T_P$ followed by $T_Q$.
--
--   This is the standard passage from a level subgroup of the theta group of $M$, on which the projection to points is bijective onto the $n$-torsion, to a normalised cocycle of isomorphisms $M \cong T_P^{*}M$ indexed by the $n$-torsion points, in the sense of Mumford's theory of theta groups and level structures. It is used in the treatment of polarisations, by [`AlgebraicGeometry.Polarisation.exists_pullback_schemeNsmul_two_iso_of_levelSubgroup`](thm.html#AlgebraicGeometry.Polarisation.exists_pullback_schemeNsmul_two_iso_of_levelSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ThetaGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules) (n : ℕ)
    (K : Subgroup (thetaGroup f L hc M))
    (hKinj : ∀ g ∈ K, ∀ h ∈ K, thetaGroup.pt f L hc M g = thetaGroup.pt f L hc M h → g = h)
    (hKpt : ∀ Q : L.AlgPoints hc k, (∃ g ∈ K, thetaGroup.pt f L hc M g = Multiplicative.ofAdd Q) ↔ n • Q = 0) :
    ∃ ψ : ∀ P : L.AlgPoints hc k, n • P = 0 →
        (M ≅ (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).obj M),
      (∀ h0 : n • (0 : L.AlgPoints hc k) = 0,
        ψ 0 h0 = ((Scheme.Modules.pullbackId A).app M).symm ≪≫
          ((Scheme.Modules.pullbackCongr (translation_toPoint_zero f L hc)).app M).symm) ∧
      (∀ (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (hPQ : n • (P + Q) = 0),
        ψ (P + Q) hPQ =
          ψ P hP ≪≫
            (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).mapIso (ψ Q hQ) ≪≫
            (Scheme.Modules.pullbackComp (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
              (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).app M ≪≫
            ((Scheme.Modules.pullbackCongr (translation_toPoint_add f L hc P Q)).app M).symm) := by sorry
