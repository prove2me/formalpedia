-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_specMap_comp_eq_of_nsmulPt_eq_one_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_specMap_comp_eq_of_nsmulPt_eq_one_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/b91ed504-8c32-5f57-8816-a20582edc86c
-- title:
--   Rigidity of m-torsion sections modulo a nilpotent ideal
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a natural number $m$. Let $S$ and $S_0$ be commutative rings with $S_0$ an $S$-algebra such that the structure map $S \to S_0$ is surjective and its kernel ideal is nilpotent (some power of it vanishes), and assume the image of $m$ in $S$ is a unit. Let $E$ be a fake elliptic curve of level data $(\Lambda, N)$ over $S$: this bundles a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} S$, a commutative relative group law $E.L$ on $E.f$ (functorial multiplication, unit and inverse on sections over any base morphism), the property bundle asserting $E.f$ smooth, proper, with connected fibres and admitting a relative group law, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms of $E.A$ over $S$ which is additive and multiplicative and satisfies the trace condition on tangent spaces, together with the remaining data of the structure. Let $\sigma$ and $\tau$ be sections of $E.f$ over the identity of $\operatorname{Spec} S$, i.e. morphisms $\operatorname{Spec} S \to E.A$ whose composite with $E.f$ is the identity, each killed by $m$ in the sense that the $m$-fold iterate of the group law, defined by $0 \mapsto$ unit section and $n+1 \mapsto \text{mul}(n\text{-fold iterate}, P)$, sends them to $E.L$'s unit section. If the two underlying morphisms become equal after precomposition with $\operatorname{Spec}$ of the map $S \to S_0$, then $\sigma = \tau$.
--
--   This is the standard rigidity statement that torsion sections of order invertible on the base are determined by their restriction to a subscheme cut out by a nilpotent ideal, here for the fake elliptic curves used in the Čerednik–Drinfeld description of quaternionic moduli. It is used in the rigidification arguments that identify level structures and their transports under Frobenius twists and $\Lambda$-actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_specMap_comp_eq_of_nsmulPt_eq_one_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_specMap_comp_eq_of_nsmulPt_eq_one_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m : ℕ)
    (S S₀ : Type) [CommRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    (hm : IsUnit ((m : ℕ) : S))
    (E : FakeEllipticCurve Λ N S)
    (σ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (hσ : nsmulPt E.L (𝟙 _) m σ = E.L.one (𝟙 _)) (hτ : nsmulPt E.L (𝟙 _) m τ = E.L.one (𝟙 _))
    (h : Spec.map (CommRingCat.ofHom (algebraMap S S₀)) ≫ σ.1 = Spec.map (CommRingCat.ofHom (algebraMap S S₀)) ≫ τ.1) :
    σ = τ := by sorry
