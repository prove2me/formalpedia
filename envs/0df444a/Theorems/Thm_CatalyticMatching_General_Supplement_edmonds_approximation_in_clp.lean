-- Prove2me | Theorems.Thm_CatalyticMatching_General_Supplement_edmonds_approximation_in_clp
-- name    : CatalyticMatching.General.Supplement.edmonds_approximation_in_clp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:11:21.187797+00:00
-- url     : https://prove2.me/theorems/a7d92ace-f720-4121-b67e-964e33e28d15
-- title:
--   Theorem 5.4 (companion theorem) — (1−ε)-approximate Edmonds’ problem in CLP
-- statement:
--   Let $\varepsilon\in(0,1)$ be a fixed real constant. Given $A_1,\dots,A_m\in F^{n\times n}$ over $\mathbb Q$, or over a finite field with
--
--   $$|F|\ge n^{2/\varepsilon+3}$$
--
--   in standard representation, there is a CLP algorithm that returns a matrix $B\in\mathcal A=\langle A_1,\dots,A_m\rangle$ with
--
--   $$\operatorname{rank}B\ \ge\ (1-\varepsilon)\cdot\operatorname{rank}(\mathcal A),\qquad \operatorname{rank}(\mathcal A)=\max_{a\in F^m}\operatorname{rank}\sum_iA_ia_i.$$
--
--   The machine and its polynomial bounds may depend on $\varepsilon$; for each $\varepsilon$ one machine works for every field in the family, every $n$, every $m$ (no basis or $m\le n^2$ promise) and every initial catalyst, and restores the catalyst. The output is the matrix itself, and it may depend on the initial catalyst. This is Theorem 1.4; it gives Corollary 5.4.1 on linear matroid matching.
--
--   Differences from the source:
--   - reading: "large enough field F such that |F| ≥ n^{2/ε+3}" in the computational setting of p.10 → ℚ, and every finite field with p^{deg f} ≥ n^{2/ε+3}; reason: p.10 specifies the field representations of the computational model (rationals; finite fields in standard explicit representation); ℚ satisfies the size bound
--   - encoding: "for any constant ε ∈ (0,1)" → ∀ real ε with 0 < ε < 1, then InCLP; reason: the machine and constants may depend on the fixed ε, as for a constant
--   - encoding: "returns a matrix A ∈ 𝒜" → output string is the n² entries of B row-major, with B ∈ span(A₁,…,A_m); reason: an explicit encoding of the returned matrix
--   - encoding: CL / CLP measured in total binary input length (Definitions 2.1–2.3 and p.10) → the published InCL / InCLP: one finite binary transition table, uniform constants C (and time exponent k), work ≤ C·(⌊log₂(L+2)⌋+1), catalyst length a fixed polynomial in L, every initial catalyst restored exactly; machine and constants precede all inputs; reason: standard tape and logarithm conventions change bounds only by constant factors; all input bits, including entry and field-description bits, are charged
--   - encoding: ℚ, and finite fields in a standard explicit representation supporting uniform TC¹ arithmetic and rank (p.10) → ℚ by reduced framed binary rationals (header bit 0); a finite field as 𝔽_p[t]/(f) with p prime and f monic irreducible given in the input (header bit 1, framed p, framed deg f, lower coefficients of f), elements by their power-basis coordinates; |F| = p^{deg f}; reason: every finite field has such a representation and it is the standard explicit one; the field description is part of the input, as required for the field size to grow with n; no arithmetic or rank oracle is supplied
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Theorem 5.4, printed/PDF p.28 (proof pp.28–30); Theorem 1.4, printed/PDF p.6

import Definitions.Def_CatalyticMatching_General_Supplement_Relations

namespace CatalyticMatching.General.Supplement

/-- Theorem 5.4 p.28 (Theorem 1.4 p.6). For each fixed real ε ∈ (0,1) and fields with
|F| ≥ n^{2/ε+3}, output B ∈ 𝒜 with rank B ≥ (1−ε)·rank(𝒜), in CLP. -/
theorem edmonds_approximation_in_clp (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    InCLP (edmondsDomain ε) (approxRelation ε) := by sorry

end CatalyticMatching.General.Supplement
