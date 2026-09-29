-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isClosedImmersion_factorsThrough_iff_nsmulPt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isClosedImmersion_factorsThrough_iff_nsmulPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/5c3bec70-fe2a-5224-a6ad-0286d19da7e4
-- title:
--   Closed subscheme [ℓ]⁻¹C∩[N]⁻¹K of a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$ and $\ell$ (no coprimality or invertibility is assumed), a commutative ring $S$ in the bottom universe, and an element $u$ of `FakeEllipticCurve.WithExtraLevel Λ N ℓ S`; thus $u.1$ consists of a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$ on $f$ whose points are $T$-morphisms over $\operatorname{Spec} S$, the abelian-scheme property bundle (smooth, proper, connected fibres, group law), two-dimensional fibres, an action of $\Lambda$ compatible with $f$ and with $L$ and satisfying the trace condition on tangent spaces, together with the level datum $u.1.\mathrm{lev} : C \to A$; and $u.2$ is an extra level structure at $\ell$, consisting of a closed immersion $u.2.\mathrm{levK} : K \to A$ whose points form an $\ell$-torsion, $\Lambda$-stable subgroup disjoint from $C$, finite flat of rank $\ell^2$ with geometric fibres $(\mathbb{Z}/\ell)^2$ when $\ell$ is invertible. The theorem asserts the existence of a scheme $C'$ and a morphism $\mathrm{lev}' : C' \to A$ which is a closed immersion, such that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every point $P$ of $A$ over $t$ (a morphism $T \to A$ composing with $f$ to $t$), $P$ factors through $\mathrm{lev}'$ (i.e. $P = P_0 \circ \mathrm{lev}'$ for some $P_0 : T \to C'$) if and only if the $\ell$-fold sum $\ell\cdot P$ formed by iterating $L.\mathrm{mul}$ from $L.\mathrm{one}$ factors through $u.1.\mathrm{lev}$ and the $N$-fold sum $N\cdot P$ factors through $u.2.\mathrm{levK}$.
--
--   This is the group-scheme plumbing step that combines a level structure and an extra level structure into a single closed subscheme, namely the scheme-theoretic intersection $[\ell]^{-1}(C)\cap[N]^{-1}(K)$ of $A$, characterised by its functor of points. It is used in the construction of fake elliptic curves with combined level data, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isClosedImmersion_factorsThrough_iff_nsmulPt.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isClosedImmersion_factorsThrough_iff_nsmulPt
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ)
    (S : Type) [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ (C' : Scheme.{0}) (lev' : C' ⟶ u.1.A), IsClosedImmersion lev' ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
        FactorsThrough lev' P ↔
          FactorsThrough u.1.lev (nsmulPt u.1.L t ℓ P) ∧ FactorsThrough u.2.levK (nsmulPt u.1.L t N P) := by sorry
