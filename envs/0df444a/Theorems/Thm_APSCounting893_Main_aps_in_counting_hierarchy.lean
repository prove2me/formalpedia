-- Prove2me | Theorems.Thm_APSCounting893_Main_aps_in_counting_hierarchy
-- name    : APSCounting893.Main.aps_in_counting_hierarchy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:01:24.001402+00:00
-- url     : https://prove2.me/theorems/e6238232-d82c-4a9e-a19e-e200315682dd
-- title:
--   Theorem 1.3 — Approximate polynomial satisfiability belongs to CH
-- statement:
--   Let $k$ be $\mathbb Q$, a number field, or a finite field given by an irreducible defining polynomial and power-basis coordinates; the finite characteristic is binary. Inputs are finite arithmetic DAGs with binary constants and $+,-,\times,/$ gates, or sparse polynomial lists with binary exponents. Every divisor must be nonzero as a rational function and every circuit output must represent a polynomial. No polynomial degree bound is promised. Write $\overline k$ for the algebraic closure of the coefficient field and $F:\overline k^{\,n}\to\overline k^{\,m}$ for the represented map.
--
--   There exist one total language $L$ and one fixed hierarchy level $j$, independent of the field, dimensions and input, such that
--
--   $$L\in C_jP,\qquad \operatorname{enc}(k,F)\in L\iff0\in\overline{F(\overline k^{\,n})}^{\,\mathrm{Zar}}$$
--
--   for every valid circuit and sparse encoding. Invalid strings and failed semantic promises may receive arbitrary answers. The class uses actual finite uniform oracle-majority machines with charged tape steps and binary queries.
--
--   The statement retains all dimensions, zero and constant outputs, arbitrary degree and coefficient height, unbounded approximating inputs, every characteristic and inseparable field behavior. It is the decision theorem itself, rather than a supplied geometric criterion or a conditional coefficient-oracle assertion.
--
--   Differences from the source:
--   - encoding: APS over rational circuits, sparse inputs and the stated number-field and finite-field extensions → one total language at one fixed hierarchy level agreeing on the tagged binary encodings of every valid input presentation; reason: encodes all coefficient fields uniformly and leaves invalid encodings and failed semantic promises unconstrained
--   - encoding: image closure over the algebraic closure of the coefficient field → the actual algebraic closure of the quotient field constructed from its irreducible presentation; reason: includes rational, number-field, inseparable and every finite-characteristic instance without a Puiseux or separability restriction
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 1.3; Remarks 1.4–1.6 and 6.7, p. 3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf; field extension p. 27

import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_CircuitInputs

set_option autoImplicit false

namespace APSCounting893.Main

/-- Theorem 1.3, Remarks 1.4–1.6 and 6.7 (pp. 3, 27).
One total language and one fixed hierarchy level decide both input representations,
uniformly over all described number fields and finite fields. Invalid encodings and failed
semantic promises impose no requirements on that language. -/
theorem aps_in_counting_hierarchy :
    ∃ L : Language, InCountingHierarchy L ∧
      (∀ (P : CoefficientPresentation) (n : ℕ) (C : ArithmeticCircuit n),
        ValidCircuit P C →
        (L ([false] ++ P.encode ++ C.encode) ↔ PolynomialAPS P (circuitPolynomials P C))) ∧
      (∀ (P : CoefficientPresentation) (n : ℕ) (S : SparseSystem n),
        validSparse P S →
        (L ([true] ++ P.encode ++ encodeSparse S) ↔ PolynomialAPS P (sparsePolynomials P S))) := by sorry

end APSCounting893.Main
