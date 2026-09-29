-- Prove2me | Theorems.Thm_CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective
-- name    : CommRingCat.isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/29497e8b-2ee9-5320-adf2-9ab4fb1a3000
-- title:
--   Pushout squares over a fibre product of rings, surjective case
-- statement:
--   Let $P,C',C'',C_0,A,A',A'',A_0$ be commutative rings (objects of `CommRingCat` in a fixed universe). Suppose given morphisms $p' : P \to C'$, $p'' : P \to C''$, $\varphi' : C' \to C_0$, $\varphi'' : C'' \to C_0$ whose square is cartesian, so that $P = C' \times_{C_0} C''$, and morphisms $a' : A \to A'$, $a'' : A \to A''$, $q' : A' \to A_0$, $q'' : A'' \to A_0$ whose square is likewise cartesian, so that $A = A' \times_{A_0} A''$. Suppose further given vertical morphisms $u : P \to A$, $u' : C' \to A'$, $u'' : C'' \to A''$, $u_0 : C_0 \to A_0$ making the remaining faces of the resulting cube commute: $p'$ followed by $u'$ equals $u$ followed by $a'$, $p''$ followed by $u''$ equals $u$ followed by $a''$, and $\varphi'$ followed by $u_0$ equals $u'$ followed by $q'$, and similarly for the double-primed maps (these last two commutativities are also part of the pushout hypotheses below). Assume that the underlying ring maps of $\varphi'$ and $\varphi''$ are surjective, and that both side squares are cocartesian, i.e. $A_0 = A' \otimes_{C'} C_0$ via $(\varphi', u', u_0, q')$ and $A_0 = A'' \otimes_{C''} C_0$ via $(\varphi'', u'', u_0, q'')$. The conclusion is that the two front squares are cocartesian as well: $(p', u, u', a')$ and $(p'', u, u'', a'')$ are pushout squares in `CommRingCat`, so that $A' = A \otimes_P C'$ and $A'' = A \otimes_P C''$.
--
--   This is the ring-theoretic core of the glueing of algebras along a fibre product of rings in which the two maps to the common quotient are surjective: cocartesianness of the two side faces of the cube propagates to the two front faces. It is used by [`AlgebraicGeometry.isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent`](thm.html#AlgebraicGeometry.isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent) as the affine chart-level input for the corresponding statement about spectra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

theorem CommRingCat.isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective
    {P C' C'' C₀ A A' A'' A₀ : CommRingCat.{u}}
    {p' : P ⟶ C'} {p'' : P ⟶ C''} {φ' : C' ⟶ C₀} {φ'' : C'' ⟶ C₀} (hC : IsPullback p' p'' φ' φ'')
    {a' : A ⟶ A'} {a'' : A ⟶ A''} {q' : A' ⟶ A₀} {q'' : A'' ⟶ A₀} (hA : IsPullback a' a'' q' q'')
    (u : P ⟶ A) (u' : C' ⟶ A') (u'' : C'' ⟶ A'') (u₀ : C₀ ⟶ A₀)
    (hu' : p' ≫ u' = u ≫ a') (hu'' : p'' ≫ u'' = u ≫ a'') (hq' : φ' ≫ u₀ = u' ≫ q') (hq'' : φ'' ≫ u₀ = u'' ≫ q'')
    (hφ' : Function.Surjective φ'.hom) (hφ'' : Function.Surjective φ''.hom)
    (hco' : IsPushout φ' u' u₀ q') (hco'' : IsPushout φ'' u'' u₀ q'') :
    IsPushout p' u u' a' ∧ IsPushout p'' u u'' a'' := by sorry
