-- Prove2me | Theorems.Thm_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction
-- name    : AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/9d825531-177c-50b2-a762-a139648fd25c
-- title:
--   Residue of a norm equals norm of the residue
-- statement:
--   Let $K$, $F$, $E$, $FE$ be fields with $K$ algebraically closed of characteristic $0$, equipped with $K$-algebra structures on $F$, $E$, $FE$, an $E$-algebra structure on $FE$ and an $F$-algebra structure on $FE$, compatible in the sense that $FE$ is a scalar tower over $K$ both through $E$ and through $F$. Assume $F$ contains an element transcendental over $K$ over which $F$ is finite (i.e. $F$ is a one-variable function field over $K$), and likewise $FE$ contains an element transcendental over $E$ over which $FE$ is finite; assume further that $FE$ is generated over $E$ by the image of $F$, i.e. the intermediate field of $FE$ generated over $E$ by $\mathrm{range}(F \to FE)$ is everything. Fix in addition $\mathrm{RatFunc}\,K$-algebra and $\mathrm{RatFunc}\,E$-algebra structures making $F$ finite over $\mathrm{RatFunc}\,K$ and $FE$ finite over $\mathrm{RatFunc}\,E$, compatibly with $K$ resp. $E$, and suppose the two variables agree: the image of $X$ under $\mathrm{RatFunc}\,E \to FE$ coincides with the image under $\mathrm{RatFunc}\,K \to F \to FE$. Let $A$ be a valuation subring of $E$ containing the image of $K$ and such that every $a \in A$ satisfies $v_A(a - k) < 1$ for some $k \in K$, i.e. the residues of $A$ are represented by $K$. Let $O$ be a valuation subring of $FE$ and $\rho : O \to F$ a ring homomorphism such that an element of $E$ lies in $A$ exactly when its image in $FE$ lies in $O$, the kernel of $\rho$ is the maximal ideal of the local ring $O$, and every $f \in F$ has image in $O$ with $\rho$ of that image equal to $f$. Then for every $g \in O$ with $\rho(g) \neq 0$, the image in $FE$ of the norm $\mathrm{Algebra.norm}_{\mathrm{RatFunc}\,E}(g)$ lies in $O$, and $\rho$ of it equals the image in $F$ of $\mathrm{Algebra.norm}_{\mathrm{RatFunc}\,K}(\rho(g))$.
--
--   This is the compatibility of the residue map of a Gauss prolongation of a constant-field extension with the norms down to the rational function fields $E(X)$ and $K(X)$; the linear-disjointness input is provided by [`AlgebraicCurve.linearIndependent_of_constantFieldExtension`](thm.html#AlgebraicCurve.linearIndependent_of_constantFieldExtension), which transports a $K$-linearly independent family in $F$ to an $E$-linearly independent family in $FE$. It is used in the reduction theory of divisors, via [`AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction`](thm.html#AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction), to compare orders of elements at a place with the orders of their reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Polynomial

theorem AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE] [FiniteDimensional (RatFunc E) FE]
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    (A : ValuationSubring E)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)
    (g : O) (hg : ρ g ≠ 0) :
    ∃ h : algebraMap (RatFunc E) FE (Algebra.norm (RatFunc E) (g : FE)) ∈ O,
      ρ ⟨_, h⟩ = algebraMap (RatFunc K) F (Algebra.norm (RatFunc K) (ρ g)) := by sorry
