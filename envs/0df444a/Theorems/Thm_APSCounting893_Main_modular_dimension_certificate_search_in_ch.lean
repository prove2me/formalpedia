-- Prove2me | Theorems.Thm_APSCounting893_Main_modular_dimension_certificate_search_in_ch
-- name    : APSCounting893.Main.modular_dimension_certificate_search_in_ch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:46:59.105974+00:00
-- url     : https://prove2.me/theorems/92f282d9-e6b6-469b-9b14-52535494df9c
-- title:
--   Uniform CH search for the largest modular Jacobian certificate
-- statement:
--   For valid rational arithmetic circuits, one fixed Counting Hierarchy oracle permits a deterministic polynomial-time machine to return the largest size of a bounded modular Jacobian certificate.
--
--   There exist a total language $A\in\mathrm{CH}$ and a total function $f\in\mathrm{FP}^{A}$ such that, for every valid circuit $C$, some natural number $r$ satisfies
--
--   $$
--   f(\operatorname{encode}(C))=\operatorname{encode}(r),\qquad
--   k\le r\iff\operatorname{Cert}(C,k)\quad\text{for all }k\ge0.
--   $$
--
--   The machine, polynomial time bound and hierarchy level precede all circuits and all input lengths. Answers outside the circuit promises are unrestricted. The certificate predicate uses integer cross multiplication, cleared Jacobian minors, bounded sparse assignments and prime residues, rather than an APS or image-dimension oracle.
--
--   Together with the mathematical certificate theorem, this is the computational part of the image-dimension milestone.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 6, Lemma 6.1 and proof, p.23. Auxiliary modular implementation of its characteristic-zero Jacobian-rank step; explicit witness bounds are proved here. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf#page=23 . Schwartz–Zippel: Mathlib 0df444a, Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean, schwartz_zippel_totalDegree; modular witness: Mathlib/NumberTheory/Chebyshev.lean, two_pow_le_mul_lcmUpto.

import Definitions.Def_APSCounting893_Main_ModularJacobianData
set_option autoImplicit false

theorem APSCounting893.Main.modular_dimension_certificate_search_in_ch :
    ∃ (A : APSCounting893.Main.Language) (f : APSCounting893.Main.Word → APSCounting893.Main.Word),
      APSCounting893.Main.InCountingHierarchy A ∧ APSCounting893.Main.FunctionInPWithOracle A f ∧
      ∀ (n : ℕ) (C : APSCounting893.Main.ArithmeticCircuit n), APSCounting893.Main.ValidCircuit .rational C →
        ∃ r : ℕ,f C.encode=APSCounting893.Main.encodeNat r ∧
          ∀ k : ℕ,k≤r ↔ APSCounting893.Main.ModularJacobianCertificate C k := by sorry
