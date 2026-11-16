-- Prove2me | Theorems.Thm_CatalyticMatching_General_Supplement_mixed_rank_deficiency_test_in_cl
-- name    : CatalyticMatching.General.Supplement.mixed_rank_deficiency_test_in_cl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:09:07.585845+00:00
-- url     : https://prove2.me/theorems/91ded643-a99f-4238-9a48-877cbb444ba8
-- title:
--   Lemma 4.5 — catalytic-logspace test of generic rank and full deficiency equality
-- statement:
--   Given a field $F$ (either $\mathbb Q$, or a finite field with at least $(r+c)^{10}$ elements in standard representation), an $r\times c$ mixed matrix $A$ over $F$ and an evaluation $A'$ of $A$, one can decide in CL whether
--
--   $$\operatorname{rank}A=\operatorname{rank}A'\ \wedge\ D(A)=D(A').$$
--
--   Here $\operatorname{rank}A$ and $D(A)$ are the rank and the row/column deficiency set of the generic matrix over $F(X)$. One fixed catalytic machine outputs the correct bit for every input and every initial catalyst, using logarithmic work space and polynomial catalytic space, and restores the catalyst. No generic rank or deficiency is supplied. This test is the stopping criterion of the algorithm of Theorem 4.6.
--
--   Differences from the source:
--   - generalization: Lemma 4.5 in §4, where F = ℚ → ℚ and every finite field in standard representation with at least (r+c)^10 elements, by one machine; reason: the §4 preamble (p.22) states that the argument adapts to sufficiently large finite fields; (r+c)^10 is the number of test values the proof enumerates; the ℚ inputs recover the printed lemma
--   - encoding: CL / CLP measured in total binary input length (Definitions 2.1–2.3 and p.10) → the published InCL / InCLP: one finite binary transition table, uniform constants C (and time exponent k), work ≤ C·(⌊log₂(L+2)⌋+1), catalyst length a fixed polynomial in L, every initial catalyst restored exactly; machine and constants precede all inputs; reason: standard tape and logarithm conventions change bounds only by constant factors; all input bits, including entry and field-description bits, are charged
--   - encoding: ℚ, and finite fields in a standard explicit representation supporting uniform TC¹ arithmetic and rank (p.10) → ℚ by reduced framed binary rationals (header bit 0); a finite field as 𝔽_p[t]/(f) with p prime and f monic irreducible given in the input (header bit 1, framed p, framed deg f, lower coefficients of f), elements by their power-basis coordinates; |F| = p^{deg f}; reason: every finite field has such a representation and it is the standard explicit one; the field description is part of the input, as required for the field size to grow with n; no arithmetic or rank oracle is supplied
--   - encoding: an r×c mixed matrix with rows L_r, columns L_c and variable set X indexed by E → Fin r → Fin c → Option F (none = indeterminate), variables = positions holding none, row/column tags Fin r ⊕ Fin c, A′_{x_i←b} = Function.update of the assignment; reason: relabeling covers every finite rectangular instance, including r = 0 or c = 0; tags keep row u and column u distinct as in L_r ∪ L_c
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Lemma 4.5, printed/PDF p.24; field setting §4 preamble p.22 and p.10

import Definitions.Def_CatalyticMatching_General_Supplement_Relations

namespace CatalyticMatching.General.Supplement

/-- Lemma 4.5 p.24. Given A and an evaluation A′, decide rank A = rank A′ ∧ D(A) = D(A′)
in CL, over ℚ and over finite fields of size at least (r+c)^10. -/
theorem mixed_rank_deficiency_test_in_cl : InCL mixedTestDomain mixedTestRelation := by sorry

end CatalyticMatching.General.Supplement
