-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors
-- name    : AlgebraicCurve.ConstantReduction.isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/094f5b4f-0c1f-5111-9fae-be47702f6166
-- title:
--   Unit values at rational places under constant reduction
-- statement:
--   Let $K$ be a field, $A$ a valuation subring of $K$, $F$ a field extension of $K$, and $\bar F$ an extension of the residue field of $A$, and assume $F/K$ has principal divisors: every nonzero $f \in F$ admits a finitely supported $D : \mathrm{Place}\,K\,F \to \mathbb{Z}$ with $D(v) = v.\mathrm{ord}(f)$ for all places $v$ and $\deg D = 0$, where $\mathrm{ord}$ is minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation and places are valuation subrings of $F$ containing $K$, proper, with principal ideals. Let $R$ be a constant reduction of $F$ over $A$ with values in $\bar F$: a valuation subring `R.integers` of $F$, a surjective ring homomorphism `R.residue` onto $\bar F$ with kernel the maximal ideal, and a map `R.placeMap` from places of $F/K$ to places of $\bar F$ over the residue field of $A$, subject to the structure's compatibilities. Let $P$ be a place of $F/K$ that is rational, i.e. $K$ surjects onto its residue field, and let $f \in F$ lie in `R.integers` with `R.residue` $\langle f\rangle \neq 0$, with $\mathrm{ord}$ of that reduction at the place `R.placeMap P` equal to $0$, and with $f$ in the valuation subring of every place $w$ satisfying `R.placeMap w = R.placeMap P`. Then $P.\mathrm{evalAt}\,f$, the preimage in $K$ under the surjection onto $P$'s residue field of the residue class of $f$, lies in $A$ and is a unit of $A$.
--
--   This is the unit principle for constant reduction of a function field: a Gauss-integral function with nonzero reduction having neither zero nor pole at the reduced place takes a value in $A^{\times}$ at a rational place of the fibre. It is used in the construction of uniform windows on modular curves, being cited by [`ModularCurve.exists_uniform_window_smul_mem_integers`](thm.html#ModularCurve.exists_uniform_window_smul_mem_integers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors.lean

import Definitions.Def_ModularCurve_FinitePlaceLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors
    {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F] [Algebra K F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    {P : Place K F} (hP : P.IsRational) {f : F} (hf : f ∈ R.integers) (hres : R.residue ⟨f, hf⟩ ≠ 0)
    (hord : (R.placeMap P).ord (R.residue ⟨f, hf⟩) = 0)
    (hfib : ∀ w : Place K F, R.placeMap w = R.placeMap P → f ∈ w.toValuationSubring) :
    ∃ h : P.evalAt f ∈ A, IsUnit (⟨P.evalAt f, h⟩ : A) := by sorry
