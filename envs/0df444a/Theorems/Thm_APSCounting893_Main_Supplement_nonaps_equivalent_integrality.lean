-- Prove2me | Theorems.Thm_APSCounting893_Main_Supplement_nonaps_equivalent_integrality
-- name    : APSCounting893.Main.Supplement.nonaps_equivalent_integrality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:10:05.593238+00:00
-- url     : https://prove2.me/theorems/54b6abdc-454f-44e7-a46e-7138e8556ce2
-- title:
--   Theorem 1.11 — Non-APS and integral closure are many-one equivalent
-- statement:
--   Under the published circuit and sparse input promises and coefficient encodings, non-existence of APS and integral-closure membership are equivalent under deterministic polynomial-time many-one reductions:
--
--   $$\mathrm{non\text{-}APS}\le_m^{\mathrm P}\mathrm{ICM},\qquad\mathrm{ICM}\le_m^{\mathrm P}\mathrm{non\text{-}APS}.$$
--
--   Both reductions preserve validity and the base coefficient presentation and have fixed machines and polynomial time bounds before all inputs. Algebraic correctness also holds over every algebraically closed field $K$: for an independent $z$, non-APS of $F$ is equivalent to integrality of $z$ over $K[zf_i]$; for any target $f$, integrality over $K[f_i]$ is equivalent to non-APS of $(uf_i^M,u,1-uf)$ for all sufficiently large integers $M$. Thus Remark 1.12 is retained without a restriction on characteristic, while binary runtime is asserted for the encoded families. This joins the two decision problems in both directions.
--
--   Differences from the source:
--   - encoding: polynomial-time reductions on the stated inputs → promise reductions between the common encoded SystemInput predicates; reason: the published coefficient presentations, division promises and binary sparse inputs are retained
--   - encoding: the equivalence works over all algebraically closed fields → fresh-variable correctness and eventual powered-system correctness over every algebraically closed K, together with uniform binary reductions on encoded families; reason: no Turing encoding of arbitrary abstract fields is presumed; the source does not specify one
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 1.11, p. 4

import Definitions.Def_APSCounting893_Main_Supplement_DecisionProblems

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Theorem 1.11 / Remark 1.12. Abstract fields have algebraic correctness;
ordinary binary computation is asserted on the finitely presented coefficient families. -/
theorem nonaps_equivalent_integrality :
    PolynomialManyOne SystemInput.Valid (fun I => ¬ I.APS)
      SystemInput.ValidIntegral SystemInput.Integral ∧
    PolynomialManyOne SystemInput.ValidIntegral SystemInput.Integral
      SystemInput.Valid (fun I => ¬ I.APS) ∧
    PoweredAlgebraicReduction ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (n m : ℕ)
      (F : PolynomialMap K n m),
      (¬ AlgebraicAPS F) ↔ IntegralOverGenerators (scaledGenerators F) (freshVariable n)) := by sorry

end APSCounting893.Main.Supplement
