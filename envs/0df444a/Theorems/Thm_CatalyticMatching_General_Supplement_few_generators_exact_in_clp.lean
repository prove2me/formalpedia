-- Prove2me | Theorems.Thm_CatalyticMatching_General_Supplement_few_generators_exact_in_clp
-- name    : CatalyticMatching.General.Supplement.few_generators_exact_in_clp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:10:49.13861+00:00
-- url     : https://prove2.me/theorems/2fcf997d-6664-4b57-8438-96aac1a3849f
-- title:
--   Remark 5.3 — exact maximum-rank matrix in CLP when fewer than ℓ generators
-- statement:
--   Fix $\varepsilon\in(0,1)$ and let $\ell=\lceil1/\varepsilon-1\rceil$. For matrix spaces $\mathcal A=\langle A_1,\dots,A_m\rangle\le F^{n\times n}$ over $\mathbb Q$, or over a finite field with $|F|\ge n^{2/\varepsilon+3}$ in standard representation, whose dimension is less than $\ell$ (in particular whenever $m<\ell$), one can compute in CLP a matrix
--
--   $$B\in\mathcal A\qquad\text{with}\qquad \operatorname{rank}B=\operatorname{rank}(\mathcal A).$$
--
--   The machine depends on $\varepsilon$; for each $\varepsilon$ it runs in polynomial time with logarithmic work space and polynomial catalytic space and restores the catalyst. This case is solved exactly; the approximation algorithm of Theorem 5.4 assumes $m\ge\ell$.
--
--   Differences from the source:
--   - generalization: m < ℓ, where the generating set is assumed to be a basis (p.26) → dim 𝒜 < ℓ for an arbitrary generating list; reason: p.26 and footnote 5 reduce any list to a basis in CLP; every list with m < ℓ has dim 𝒜 ≤ m < ℓ, so the printed case is included
--   - reading: the setting of Theorem 5.4, with S the first n^c elements of F and |S| > n → field hypothesis |F| ≥ n^{2/ε+3} of Theorem 5.4; reason: the remark is part of the proof setting of Theorem 5.4; for n ≥ 2 this gives |S| = n^{2ℓ+3} > n, and n ≤ 1 is included
--   - reading: "polynomial time and O_ε(log n) workspace, apart from the catalytic space used by the rank subroutine. Hence this case can be solved exactly in CLP" → InCLP for each fixed ε; reason: the conclusion of the remark is CLP; the O_ε(log n) count is the enumeration part of the procedure, and together with the rank subroutine the total is within the CLP work bound
--   - encoding: CL / CLP measured in total binary input length (Definitions 2.1–2.3 and p.10) → the published InCL / InCLP: one finite binary transition table, uniform constants C (and time exponent k), work ≤ C·(⌊log₂(L+2)⌋+1), catalyst length a fixed polynomial in L, every initial catalyst restored exactly; machine and constants precede all inputs; reason: standard tape and logarithm conventions change bounds only by constant factors; all input bits, including entry and field-description bits, are charged
--   - encoding: ℚ, and finite fields in a standard explicit representation supporting uniform TC¹ arithmetic and rank (p.10) → ℚ by reduced framed binary rationals (header bit 0); a finite field as 𝔽_p[t]/(f) with p prime and f monic irreducible given in the input (header bit 1, framed p, framed deg f, lower coefficients of f), elements by their power-basis coordinates; |F| = p^{deg f}; reason: every finite field has such a representation and it is the standard explicit one; the field description is part of the input, as required for the field size to grow with n; no arithmetic or rank oracle is supplied
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Remark 5.3, printed/PDF pp.27–28

import Definitions.Def_CatalyticMatching_General_Supplement_Relations

namespace CatalyticMatching.General.Supplement

/-- Remark 5.3 pp.27--28. For each fixed ε ∈ (0,1), instances with m < ℓ = ⌈1/ε − 1⌉
(dim 𝒜 < ℓ, in particular m < ℓ) are solved exactly in CLP: output a maximum-rank matrix of the span. -/
theorem few_generators_exact_in_clp (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    InCLP (fewGeneratorsDomain ε) (exactSpanRelation ε) := by sorry

end CatalyticMatching.General.Supplement
