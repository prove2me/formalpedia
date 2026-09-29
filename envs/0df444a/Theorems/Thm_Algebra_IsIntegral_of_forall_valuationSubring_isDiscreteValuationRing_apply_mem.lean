-- Prove2me | Theorems.Thm_Algebra_IsIntegral_of_forall_valuationSubring_isDiscreteValuationRing_apply_mem
-- name    : Algebra.IsIntegral.of_forall_valuationSubring_isDiscreteValuationRing_apply_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/d0b5b892-1031-5979-91ec-6b72402f5557
-- title:
--   Discrete valuative criterion for integrality
-- statement:
--   Let $R$ and $B$ be commutative rings in a common universe, with $R$ Noetherian, and let $B$ be an $R$-algebra of finite type. Assume the following discrete valuative hypothesis: for every field $K$, every valuation subring $V \subseteq K$ whose underlying ring is a discrete valuation ring, and every ring homomorphism $\varphi : B \to K$ such that $\varphi(\mathrm{algebraMap}_{R,B}(r)) \in V$ for all $r \in R$, one has $\varphi(b) \in V$ for every $b \in B$; that is, any $K$-valued point of $B$ carrying $R$ into $V$ carries all of $B$ into $V$. The conclusion is that $B$ is integral over $R$, i.e. every element of $B$ satisfies a monic polynomial with coefficients in the image of $R$. Note that the valuation subrings tested are restricted to discrete ones, and that $K$ is quantified over the same universe $u$ as $R$ and $B$.
--
--   This is the discrete form of the valuative criterion characterising integral (equivalently, affine universally closed) morphisms: over a Noetherian base and for an algebra of finite type, discrete valuation rings suffice as test objects. It is applied in the construction of full-level modular curves to prove integrality of the fine moduli ring over the $j$-line, where the geometric input about elliptic curves with level structure is available over discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsIntegral_of_forall_valuationSubring_isDiscreteValuationRing_apply_mem.lean

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.IsIntegral.of_forall_valuationSubring_isDiscreteValuationRing_apply_mem
    (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (h : ∀ (K : Type u) [Field K] (V : ValuationSubring K), IsDiscreteValuationRing V →
      ∀ (φ : B →+* K), (∀ r : R, φ (algebraMap R B r) ∈ V) → ∀ b : B, φ b ∈ V) :
    Algebra.IsIntegral R B := by sorry
