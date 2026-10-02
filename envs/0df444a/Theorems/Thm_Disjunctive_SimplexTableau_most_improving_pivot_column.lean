-- Prove2me | Theorems.Thm_Disjunctive_SimplexTableau_most_improving_pivot_column
-- name    : Disjunctive.SimplexTableau.most_improving_pivot_column
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:53:35.506416+00:00
-- url     : https://prove2.me/theorems/8a76ab27-5e8b-4e1f-82d5-eacddd8a29c8
-- title:
--   Theorem 9.3 — the most-improving pivot column
-- statement:
--   This is Theorem 9.3 of Balas's *Disjunctive Programming*, the goal theorem of this
--   mission: characterizing which column to pivot on, in a chosen row `i`, to obtain the strongest
--   possible cut from row `k`.
--
--   The pivot column in row `i` most improving with respect to the cut from row `k` is indexed by
--   `l*∈J` minimizing `f⁺(γ_l)` (if `ā_klā_il<0`) or `f⁻(γ_l)` (if `ā_klā_il>0`), over all `l∈J`
--   satisfying `-ā_k0/ā_i0 < γ_l < (1-ā_k0)/ā_i0` (the range within which the composite row (9.10)
--   still yields a genuine 0-1 disjunctive cut on `x_k`), `γ_l := -ā_kl/ā_il`.
--
--   **Correcting the truncated statement.** `BRIEF.md`'s own quoted excerpt for the range condition
--   was marked as truncated ("verify the exact inequality against the page... `statements.jsonl`'s
--   extraction truncates it mid-condition"); the full condition, confirmed directly against the PDF
--   (p. 113-114, PDF 119-120), is exactly `-ā_k0/ā_i0 < γ_l < (1-ā_k0)/ā_i0` — matching the range
--   derived earlier in the same section (p. 113: "if γ satisfies `-āk0/āi0 < γ < (1-āk0)/āi0`").
--
--   The book's proof derives `f⁺,f⁻` by adding row `i` (weight `γ`) to row `k`, forming the composite
--   row (9.10), deriving the resulting simple disjunctive cut's coefficients, eliminating `γ²` terms
--   by subtracting a multiple of row `i`, and scaling by the sum of multipliers to restore CGLP
--   normalization — yielding exactly `f⁺,f⁻` as the resulting objective values.
--
--   **Formalization Note.** Stated as existence of a minimizing `l*` over the (necessarily finite,
--   since `J : Finset (Fin n)`) valid range, matching what "is indexed by that `l*` that minimizes..."
--   asserts; existence of at least one valid `l` in the stated range is not separately hypothesized,
--   matching the book's own unconditional phrasing (it presupposes, as in its own algorithmic
--   context, that an improving pivot is being sought because one exists).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 113, Theorem 9.3

import Mathlib
import Definitions.Def_Disjunctive_SimplexTableau_Tableau
import Definitions.Def_Disjunctive_SimplexTableau_Eval

namespace Disjunctive.SimplexTableau

/-- Theorem 9.3 (Balas §9.2, p. 113-114), the goal theorem of this mission: the pivot column in
row `i` of the (LP) simplex tableau most improving with respect to the cut from row `k` is indexed
by some `l* ∈ J` in the valid pivoting range `-ā_k0/ā_i0 < γ_l < (1-ā_k0)/ā_i0` that minimizes
`FEval` (`f⁺(γ_l)` if `ā_kl ā_il < 0`, `f⁻(γ_l)` if `ā_kl ā_il > 0`) over every `l ∈ J` in that
same range. The pivoting range is required to be nonempty: with no column of `J` in it (in
particular with `J = ∅`) no such `l*` exists and the conclusion is false. -/
theorem most_improving_pivot_column {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n)
    (J : Finset (Fin n)) (xbar : Fin n → ℝ)
    (hrange : ∃ l ∈ J, -(Abar0 Atil btil ι k) / Abar0 Atil btil ι i < GammaOf Atil ι k i l ∧
      GammaOf Atil ι k i l < (1 - Abar0 Atil btil ι k) / Abar0 Atil btil ι i) :
    ∃ lstar ∈ J,
      (-(Abar0 Atil btil ι k) / Abar0 Atil btil ι i < GammaOf Atil ι k i lstar ∧
          GammaOf Atil ι k i lstar < (1 - Abar0 Atil btil ι k) / Abar0 Atil btil ι i) ∧
        ∀ l ∈ J, (-(Abar0 Atil btil ι k) / Abar0 Atil btil ι i < GammaOf Atil ι k i l ∧
            GammaOf Atil ι k i l < (1 - Abar0 Atil btil ι k) / Abar0 Atil btil ι i) →
          FEval Atil btil ι k i J xbar lstar ≤ FEval Atil btil ι k i J xbar l := by sorry

end Disjunctive.SimplexTableau
