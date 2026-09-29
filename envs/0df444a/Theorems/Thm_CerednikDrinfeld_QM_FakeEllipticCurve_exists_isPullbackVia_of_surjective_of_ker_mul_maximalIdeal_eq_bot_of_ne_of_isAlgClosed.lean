-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_of_surjective_of_ker_mul_maximalIdeal_eq_bot_of_ne_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_of_surjective_of_ker_mul_maximalIdeal_eq_bot_of_ne_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/e8a5cbc3-8b00-5e45-b007-f21af94fbeea
-- title:
--   Lifting level-one fake elliptic curves along small surjections
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order maximal among orders containing it), and let $p$ be a prime with $p \neq q$, $p \neq q'$. Let $B$ and $B'$ be Artinian local commutative rings, the residue field of $B$ being algebraically closed of characteristic $p$, and let $\sigma : B' \to B$ be a surjective ring homomorphism whose kernel satisfies $\ker\sigma \cdot \mathfrak{m}_{B'} = 0$ (a small extension). Then for every fake elliptic curve $E$ over $B$ of level $1$ — an abelian scheme $E.f : E.A \to \operatorname{Spec} B$ with commutative relative group law, all fibres of dimension $2$, an action of $\Lambda$ by endomorphisms over $B$ which is additive, anti-multiplicative and unital, subject to the trace condition on tangent spaces, together with the level datum $E.\mathrm{lev} : E.C \to E.A$ — there exist a fake elliptic curve $E'$ over $B'$ of level $1$ and a morphism $g : E.A \to E'.A$ exhibiting $E$ as the pullback of $E'$ along $\operatorname{Spec}\sigma$: the square formed by $g$, $E.f$, $E'.f$ and $\operatorname{Spec}\sigma$ is a pullback, $g$ carries the relative group law of $E$ to that of $E'$ on points over any base $T \to \operatorname{Spec} B$, satisfies $E.\mathrm{act}(x) \,\text{followed by}\, g = g$ followed by $E'.\mathrm{act}(x)$ for every $x \in \Lambda$, and sends points factoring through $E.\mathrm{lev}$ to points factoring through $E'.\mathrm{lev}$.
--
--   This is the unobstructedness of the deformation problem for fake elliptic curves with $\Lambda$-multiplication at a residue characteristic $p$ away from the two ramified primes: every such curve over an Artinian local ring lifts through a small surjection, compatibly with the group law, the $\Lambda$-action and the level datum. It feeds the construction of towers of lifts over complete discrete valuation rings, and thence the power-series (formal) models used in the Čerednik–Drinfeld description of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_of_surjective_of_ker_mul_maximalIdeal_eq_bot_of_ne_of_isAlgClosed.lean

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
open IsLocalRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_of_surjective_of_ker_mul_maximalIdeal_eq_bot_of_ne_of_isAlgClosed
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) (hpq' : p ≠ q')
    (B B' : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B'] [IsLocalRing B'] [IsArtinianRing B']
    [CharP (ResidueField B) p] [IsAlgClosed (ResidueField B)]
    (σ : B' →+* B) (hσ : Function.Surjective σ) (hsmall : RingHom.ker σ * maximalIdeal B' = ⊥)
    (E : FakeEllipticCurve Λ 1 B) :
    ∃ (E' : FakeEllipticCurve Λ 1 B') (g : E.A ⟶ E'.A), FakeEllipticCurve.IsPullbackVia σ E' E g := by sorry
