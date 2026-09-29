-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_ptZ_eq_of_iso_of_isPullback_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.ptZ_eq_of_iso_of_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/3520e47f-fe59-5c53-8851-0c1e9e9e2c11
-- title:
--   Point map on QM structures is isomorphism-invariant
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a map $\mathrm{star}:\Lambda\to\Lambda$, a family $\beta:\mathrm{Fin}\,4\to\Lambda$, and naturals $d,m$ with $3\le m$. Let $R$ be a commutative ring in which $m$ is a unit and let $X$ be a polarised abelian scheme of relative dimension $2$, degree $d$ and level $m$ over $R$: an abelian scheme $X.A\to\operatorname{Spec}R$ with commutative relative group law, fibres of topological Krull dimension $2$, four $m$-torsion sections $X.P$ forming a basis of the $m$-torsion on every algebraically closed geometric fibre, and an invertible module $X.\mathrm{pol}$ that is very ample by sections with geometric fibre $H^0$-rank $d$. Let $\zeta:Z\to\operatorname{Spec}R$ be a morphism of schemes, and let $\mathrm{pt}_Z$ assign, to every commutative ring $T$, ring homomorphism $\varphi:R\to T$, polarised abelian scheme $X'$ of the same invariants over $T$, witness that $X'$ is a base change of $X$ along $\varphi$ (an isomorphism of $X'.A$ with the fibre product, compatible with the group laws, the level sections and the polarisations), and QM structure $s'$ on $X'$ — that is, a map $\mathrm{act}:\Lambda\to\mathrm{End}(X'.A)$ over the base with $\mathrm{act}(1)=\mathrm{id}$, $\mathrm{act}(xy)=\mathrm{act}(x)\circ\mathrm{act}(y)$, additive in $x$ and additive for the group law, satisfying the trace condition $\operatorname{tr}(\mathrm{act}(x))=n$ on geometric tangent spaces whenever $x+\mathrm{star}(x)=n$, together with a section $P$ with $\mathrm{act}(\beta_j)(P)=X'.P_j$ for all $j$ and a canonical polarisation datum $\mathrm{polE}$ relative to $\mathrm{star}$ with $X'.\mathrm{pol}$ locally isomorphic on the base to $\mathrm{polE}^{\otimes 3}$ — a morphism $\operatorname{Spec}T\to Z$ whose composite with $\zeta$ is $\operatorname{Spec}\varphi$. Assume $\mathrm{pt}_Z$ is natural: whenever $\psi:T\to T'$ satisfies $\psi\circ\varphi=\varphi'$ and $s'$, $s''$ are QM structures on base changes $X'$, $X''$ of $X$ along $\varphi$, $\varphi'$ with $\mathrm{QMStructure.IsPullback}\ \psi\ s'\ s''$, the morphism attached to $s''$ is $\operatorname{Spec}\psi$ followed by the morphism attached to $s'$. Then for a single $\varphi:R\to T$, two base changes $X'$, $X''$ of $X$ along $\varphi$ and QM structures $s'$ on $X'$, $s''$ on $X''$ that are isomorphic in the sense of `QMStructure.Iso` (an isomorphism $X'.A\cong X''.A$ over $\operatorname{Spec}T$ respecting the group laws, the level sections, the polarisations locally on the base, the $\Lambda$-actions and the distinguished sections), the two values $\mathrm{pt}_Z\,T\,\varphi\,X'\,s'$ and $\mathrm{pt}_Z\,T\,\varphi\,X''\,s''$ coincide.
--
--   This is the rigidity step which shows that a natural point map on pairs (base change of $X$, QM structure) factors through isomorphism classes, the naturality hypothesis being used only along the identity of $T$; it rests on the fact that at level $m\ge 3$ a morphism of polarised abelian schemes compatible with the structure over a fixed base change is unique. It is used in the construction of schemes representing QM structures on polarised abelian surfaces, both in the patching of transition data over affine opens and in the global representability statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_ptZ_eq_of_iso_of_isPullback_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.ptZ_eq_of_iso_of_isPullback_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ}
    {d m : ℕ} (hm : 3 ≤ m) {R : Type} [CommRing R] (hm' : IsUnit ((m : ℕ) : R))
    (X : PolarisedAbelianScheme 2 d m R) {Z : Scheme.{0}} (ζ : Z ⟶ Spec (CommRingCat.of R))
    (ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T),
      PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ)
    (hnat : ∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : R →+* T) (φ' : R →+* T') (ψ : T →+* T')
      (hψ : ψ.comp φ = φ')
      (X' : PolarisedAbelianScheme 2 d m T) (X'' : PolarisedAbelianScheme 2 d m T')
      (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ' X X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.IsPullback ψ s' s'' →
      (ptZ T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ X' hX' s').1)
    (T : Type) [CommRing T] (φ : R →+* T) (X' X'' : PolarisedAbelianScheme 2 d m T)
    (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ X X'')
    (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X'') (h : QMStructure.Iso s' s'') :
    ptZ T φ X' hX' s' = ptZ T φ X'' hX'' s'' := by sorry
