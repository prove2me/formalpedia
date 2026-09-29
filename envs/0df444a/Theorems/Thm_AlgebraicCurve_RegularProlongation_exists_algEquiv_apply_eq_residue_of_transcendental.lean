-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_algEquiv_apply_eq_residue_of_transcendental
-- name    : AlgebraicCurve.RegularProlongation.exists_algEquiv_apply_eq_residue_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/7a927f5c-b61d-55c3-814e-8ba8e43525c8
-- title:
--   Recognising the residue field of a regular prolongation
-- statement:
--   Let $V$ be a valuation subring of a field $L$, with residue field $k = \mathrm{ResidueField}(V)$, let $F'$ be a field extension of $L$ and $Fb$ a field extension of $k$, and let $R$ be a regular prolongation of $V$ to $F'$ with residue field $Fb$: that is, a valuation subring $R.\mathrm{integers}$ of $F'$ together with a ring homomorphism $R.\mathrm{residue}\colon R.\mathrm{integers}\to Fb$ such that $\mathrm{algebraMap}\,L\,F'(x)\in R.\mathrm{integers}$ exactly for $x\in V$, the residue map is surjective with kernel the maximal ideal of $R.\mathrm{integers}$, it agrees on the image of $V$ with the residue map of $V$ followed by $k\to Fb$, and every nonzero $f\in F'$ has an $L$-multiple lying in $R.\mathrm{integers}$ with nonzero residue. Let $y\in R.\mathrm{integers}$ be such that $F'$ is finite-dimensional over the intermediate field $L(y)$ and the residue $R.\mathrm{residue}(y)$ is transcendental over $k$. Let $F$ be a field extension of $k$ and $\Lambda$ a subring of $F'$ contained in $R.\mathrm{integers}$, containing $y$ and the image of $V$ under $L\to F'$, each element of which satisfies a monic polynomial with coefficients in the image of $V[y]$ (formally: a monic $P\in (V[X])[X]$ vanishing on $f$ under the evaluation sending $X\mapsto y$ in the coefficients). Let $\rho\colon\Lambda\to F$ be a ring homomorphism which on the image of $V$ is the residue map of $V$ followed by $k\to F$, whose kernel is annihilated by $R.\mathrm{residue}$, and which is such that every $z\in F$ can be written with $z\,\rho(h)=\rho(f)$ for some $f,h\in\Lambda$ with $\rho(h)\neq 0$. Assume finally that $F$ is finite-dimensional over the intermediate field $k(\rho(y))$ and that $\mathrm{finrank}_{L(y)}F'\le \mathrm{finrank}_{k(\rho(y))}F$. Then there is an isomorphism $\theta\colon F\to Fb$ of $k$-algebras with $\theta(\rho(f)) = R.\mathrm{residue}(f)$ for every $f\in\Lambda$.
--
--   This is the recognition step in Deuring-style reduction theory: under the stated integrality, compatibility and degree conditions, a reduction map $\rho$ defined on an integral model $\Lambda$ is identified, up to a canonical $k$-algebra isomorphism of its fraction field $F$ with the residue field of $R$, with the residue map of the prolongation itself. It is used in the construction of good constant reductions of elliptic function fields, through [`AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder`](thm.html#AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder), and relies on the fundamental-inequality bound [`AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le`](thm.html#AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le) for the surjectivity of $\theta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_algEquiv_apply_eq_residue_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

universe u v w w'

theorem AlgebraicCurve.RegularProlongation.exists_algEquiv_apply_eq_residue_of_transcendental
    {L : Type u} [Field L] (V : ValuationSubring L)
    {F' : Type v} [Field F'] [Algebra L F']
    {Fb : Type w} [Field Fb] [Algebra (IsLocalRing.ResidueField V) Fb]
    (R : RegularProlongation V F' Fb)
    (y : F') (hy : y ∈ R.integers)
    [FiniteDimensional (IntermediateField.adjoin L ({y} : Set F')) F']
    (htr : Transcendental (IsLocalRing.ResidueField V) (R.residue ⟨y, hy⟩))
    {F : Type w'} [Field F] [Algebra (IsLocalRing.ResidueField V) F]
    (Λ : Subring F') (hΛ : ∀ f : F', f ∈ Λ → f ∈ R.integers)
    (hyΛ : y ∈ Λ) (hVΛ : ∀ a : V, algebraMap L F' a ∈ Λ)
    (hint : ∀ f : Λ, ∃ P : (Polynomial V)[X], P.Monic ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F').comp (algebraMap V L)) y)
        (f : F') P = 0)
    (ρ : Λ →+* F)
    (hρV : ∀ a : V, ρ ⟨algebraMap L F' a, hVΛ a⟩ =
      algebraMap (IsLocalRing.ResidueField V) F (IsLocalRing.residue V a))
    (hker : ∀ f : Λ, ρ f = 0 → R.residue ⟨f, hΛ f f.2⟩ = 0)
    (hfrac : ∀ z : F, ∃ f h : Λ, ρ h ≠ 0 ∧ z * ρ h = ρ f)
    [FiniteDimensional
      (IntermediateField.adjoin (IsLocalRing.ResidueField V) ({ρ ⟨y, hyΛ⟩} : Set F)) F]
    (hdeg : Module.finrank (IntermediateField.adjoin L ({y} : Set F')) F' ≤
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField V) ({ρ ⟨y, hyΛ⟩} : Set F)) F) :
    ∃ θ : F ≃ₐ[IsLocalRing.ResidueField V] Fb, ∀ f : Λ, θ (ρ f) = R.residue ⟨f, hΛ f f.2⟩ := by sorry
