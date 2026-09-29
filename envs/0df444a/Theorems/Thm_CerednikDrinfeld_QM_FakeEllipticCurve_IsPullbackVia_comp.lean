-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/585f13ec-54ad-533d-afc5-55fd99cfa9f0
-- title:
--   Composition of base-change comparisons for fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$; let $S,S',S''$ be commutative rings and $\varphi : S \to S'$, $\psi : S' \to S''$ ring homomorphisms. Let $E$, $E'$, $E''$ be fake elliptic curves with $\Lambda$-action and level $N$ over $S$, $S'$, $S''$ respectively, and let $g : E'.A \to E.A$, $g' : E''.A \to E'.A$ be morphisms of schemes. Assume `FakeEllipticCurve.IsPullbackVia` holds for $\varphi, E, E', g$ and for $\psi, E', E'', g'$; that is, in each case the square formed by the comparison morphism, the two structure morphisms and $\mathrm{Spec}$ of the given ring map is cartesian, the comparison morphism carries the relative group law on the upper total space to the law on the lower one (on $T$-points over any base morphism $t'$), it intertwines the $\Lambda$-actions in the sense $\mathrm{act}\,x$ followed by the comparison equals the comparison followed by $\mathrm{act}\,x$ for every $x \in \Lambda$, and every $T$-point factoring through the level structure $\mathrm{lev}$ of the upper curve has its image under the comparison factoring through the level structure of the lower curve. The conclusion is that `FakeEllipticCurve.IsPullbackVia` holds for $\psi \circ \varphi$, $E$, $E''$ and the composite $g'$ followed by $g$.
--
--   This is the transitivity (composability) of base change for fake elliptic curves in the form where the comparison morphism is named rather than merely asserted to exist: pasting of two cartesian squares, together with compatibility of the group law, the quaternionic action and the level data. It is used throughout the construction of the moduli of fake elliptic curves, for instance in the uniqueness statements for morphisms induced by isogeny pairs and in the handling of rigidifications.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open IsLocalRing

theorem CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (E'' : FakeEllipticCurve Λ N S'')
    (g : E'.A ⟶ E.A) (g' : E''.A ⟶ E'.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g) (hg' : FakeEllipticCurve.IsPullbackVia ψ E' E'' g') :
    FakeEllipticCurve.IsPullbackVia (ψ.comp φ) E E'' (g' ≫ g) := by sorry
