-- Prove2me | Theorems.Thm_CatalyticMatching_General_Supplement_mixed_rank_completion_in_clp
-- name    : CatalyticMatching.General.Supplement.mixed_rank_completion_in_clp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:09:35.586462+00:00
-- url     : https://prove2.me/theorems/aeda5aba-1d97-4a4c-8bdd-374bf7984e71
-- title:
--   Theorem 4.6 (companion theorem) — maximum-rank completion of mixed matrices in CLP
-- statement:
--   Let $A$ be an $r\times c$ mixed matrix with variables $X$ indexed by $E$, and $n=r+c$, over $\mathbb Q$ or over a finite field with at least $n^{10}$ elements in standard representation. There is a CLP procedure that outputs both
--
--   1. the generic rank $\operatorname{rank}A$ over $F(X)$, and
--   2. an assignment to $X$ whose evaluation $A'$ satisfies $\operatorname{rank}A'=\operatorname{rank}A$.
--
--   One fixed catalytic machine works for every field, dimension and initial catalyst, running in polynomial time with logarithmic work space and polynomial catalytic space, and restores the catalyst; the assignment may depend on the initial catalyst. This is Theorem 1.2: the maximum rank completion problem for mixed matrices over sufficiently large fields is in CLP. It contains linear matroid intersection (Corollary 4.6.1).
--
--   Differences from the source:
--   - generalization: Theorem 4.6 with F = ℚ; Theorem 1.2 and the §4 preamble: sufficiently large finite fields with indexed distinct test elements → one machine for ℚ and for every finite field with |F| ≥ (r+c)^10; reason: (r+c)^10 is the number of distinct test values the proof uses (n^10, n = r + c); a fixed explicit threshold is stronger than an unspecified "sufficiently large" one, and the ℚ inputs recover Theorem 4.6 exactly
--   - encoding: hypothesis "E of size m ≤ n²" → no hypothesis; reason: m ≤ rc ≤ (r+c)² holds for every mixed matrix, so the condition excludes nothing
--   - encoding: CL / CLP measured in total binary input length (Definitions 2.1–2.3 and p.10) → the published InCL / InCLP: one finite binary transition table, uniform constants C (and time exponent k), work ≤ C·(⌊log₂(L+2)⌋+1), catalyst length a fixed polynomial in L, every initial catalyst restored exactly; machine and constants precede all inputs; reason: standard tape and logarithm conventions change bounds only by constant factors; all input bits, including entry and field-description bits, are charged
--   - encoding: ℚ, and finite fields in a standard explicit representation supporting uniform TC¹ arithmetic and rank (p.10) → ℚ by reduced framed binary rationals (header bit 0); a finite field as 𝔽_p[t]/(f) with p prime and f monic irreducible given in the input (header bit 1, framed p, framed deg f, lower coefficients of f), elements by their power-basis coordinates; |F| = p^{deg f}; reason: every finite field has such a representation and it is the standard explicit one; the field description is part of the input, as required for the field size to grow with n; no arithmetic or rank oracle is supplied
--   - encoding: an r×c mixed matrix with rows L_r, columns L_c and variable set X indexed by E → Fin r → Fin c → Option F (none = indeterminate), variables = positions holding none, row/column tags Fin r ⊕ Fin c, A′_{x_i←b} = Function.update of the assignment; reason: relabeling covers every finite rectangular instance, including r = 0 or c = 0; tags keep row u and column u distinct as in L_r ∪ L_c
--   - encoding: output "rank A and an assignment" → framed binary rank followed by the variable values in row-major order of positions; reason: an explicit self-delimiting output string carrying both parts
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Theorem 4.6, printed/PDF p.24 (proof pp.24–26); Theorem 1.2, printed/PDF p.5; field setting §4 preamble p.22

import Definitions.Def_CatalyticMatching_General_Supplement_Relations

namespace CatalyticMatching.General.Supplement

/-- Theorem 4.6 p.24 (Theorem 1.2 p.5). Output both rank A and an assignment A′ with
rank A′ = rank A, in CLP, over ℚ and over finite fields of size at least (r+c)^10. -/
theorem mixed_rank_completion_in_clp : InCLP completionDomain completionRelation := by sorry

end CatalyticMatching.General.Supplement
