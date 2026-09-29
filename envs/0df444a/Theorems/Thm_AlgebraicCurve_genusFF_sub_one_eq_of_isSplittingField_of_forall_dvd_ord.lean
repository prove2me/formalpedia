-- Prove2me | Theorems.Thm_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord
-- name    : AlgebraicCurve.genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/9c467d9e-a6be-547c-a075-ded1160caf4a
-- title:
--   Genus of an unramified Kummer cover of prime degree
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero and let $F$ be a field equipped with an $L$-algebra structure which is a one-variable function field over $L$ in the sense that some $x \in F$ is transcendental over $L$ and $F$ is finite-dimensional over the intermediate field $L(x) =$ `IntermediateField.adjoin L {x}`. Let $q$ be a prime and let $f \in F$ be an element that is not a $q$-th power, i.e. $g^q \neq f$ for every $g \in F$. Assume that $q$ divides $P.\mathrm{ord}\,f$ for every place $P$ of $F$ over $L$, where a place is a valuation subring of $F$ which contains the image of $L$, is not all of $F$, and is a principal ideal ring, and where $\mathrm{ord}$ is minus the logarithm of the value of $f$ under the associated height-one-spectrum valuation with values in $\mathbb{Z}^{m0}$. Let $F'$ be a field which is an $F$-algebra and an $L$-algebra, with $L \to F \to F'$ a scalar tower, and which is a splitting field over $F$ of $X^q - f$. Then, as integers,
--   $$\mathrm{genusFF}(L, F') - 1 = q\,\bigl(\mathrm{genusFF}(L, F) - 1\bigr),$$
--   where $\mathrm{genusFF}(L, \cdot)$ denotes the $L$-dimension of the first adelic cohomology group $H^1$ of the zero divisor.
--
--   This is the Riemann–Hurwitz formula for a degree-$q$ Kummer cover $F' = F(f^{1/q})$ which is everywhere unramified, the hypothesis that $q$ divides all orders of $f$ forcing trivial ramification in residue characteristic zero; the genus is measured in the adelic $H^1$ form, and the proof passes through the Riemann–Roch and Weil duality packages for curves over an algebraically closed base. It feeds the construction of regular prolongations used to produce $q$-th powers from residual $q$-th powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {q : ℕ} [Fact q.Prime] {f : F} (hf : ∀ g : F, g ^ q ≠ f)
    (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C f)] :
    (genusFF L F' : ℤ) - 1 = q * ((genusFF L F : ℤ) - 1) := by sorry
