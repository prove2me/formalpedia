-- Prove2me | Theorems.Thm_APSCounting893_Main_Supplement_aps_iff_fresh_nonintegral
-- name    : APSCounting893.Main.Supplement.aps_iff_fresh_nonintegral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:09:06.96459+00:00
-- url     : https://prove2.me/theorems/79402db3-8668-4a22-a64f-7829154f6e58
-- title:
--   Lemma 7.11 — Fresh-variable APS/non-integrality equivalence
-- statement:
--   Let $K$ be any algebraically closed field, let $F=(f_1,\ldots,f_m)\in K[x_1,\ldots,x_n]^m$, and let $z$ be independent of the $x$ variables. Then
--
--   $$0\in\overline{F(K^n)}\quad\Longleftrightarrow\quad z\text{ is not integral over }K[zf_1,\ldots,zf_m].$$
--
--   The specified transformation appends $z$ and multiplies each old output by it. On the paper's finitely encoded coefficient families it is a deterministic polynomial-time many-one reduction from APS to non-integrality, producing a valid target on every valid source. The algebraic iff has no restriction on characteristic or field cardinality. This is the support for the reverse direction of Theorem 1.11.
--
--   Differences from the source:
--   - encoding: a fresh variable z and polynomial-time transformation → z is the last coordinate; freshCircuit specifies the DAG transformation, after binary-power sparse-to-circuit conversion; reason: reindexing changes no polynomial or instance; one charged empty-oracle machine computes its bit-string function
--   - encoding: algebraic correctness over K and runtime for input polynomials → arbitrary algebraically closed K in the iff and published encoded fields in the runtime clause; reason: an abstract field is not assigned a fictitious finite Turing encoding
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Lemma 7.11, p. 32

import Definitions.Def_APSCounting893_Main_Supplement_DecisionProblems

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Lemma 7.11: the closure iff over every algebraically closed field, and the
polynomial-time bound for its specified syntactic construction over encoded fields. -/
theorem aps_iff_fresh_nonintegral :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (n m : ℕ)
      (F : PolynomialMap K n m),
      AlgebraicAPS F ↔ ¬ IntegralOverGenerators (scaledGenerators F) (freshVariable n)) ∧
    FreshVariableReduction := by sorry

end APSCounting893.Main.Supplement
