-- Prove2me | Theorems.Thm_FlexMargin_remark_def21_def22
-- name    : FlexMargin.remark_def21_def22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:45:27.241471+00:00
-- url     : https://prove2.me/theorems/cabbc94d-4db3-4289-8faa-fc8c9955d33f
-- title:
--   Remark after Definition 2.2: Definition 2.1 is Definition 2.2 with a constant centre
-- statement:
--   For any partition of the products into categories and any uncertainty set $U\subset\mathbb R^n$: $U$ is part-wise independently symmetric (Definition 2.1) if and only if $U$ is part-wise independently symmetric around some $\mu$ with $\mu_1=\dots=\mu_n$ (Definition 2.2).
--
--   This is why Theorem 2(a), stated for Definition 2.2 sets, applies to the Definition 2.1 sets of Theorem 3.
--
--   Differences from the source:
--   - encoding: μ with μ_i = μ_j for all i, j → the constant vector fun _ => c for some real c; reason: same vectors
--   - encoding: clause (2): for each t, any σ^t ∈ Ω(s_t) → all category-preserving permutations of Fin n; reason: a category-preserving permutation is a product of within-category ones and conversely; same sets
--   - reading: Definition 2.2: E := {d − µ | d ∈ U} is part-wise independently symmetric, and Definition 2.1 is stated for sets ⊂ ℝ^n_+ → the sign condition is imposed on U only (IsPartwiseSymmAround); E satisfies clauses (1)–(2) of Definition 2.1 (IsPartwiseSymmCore) and may have negative entries; reason: E is the set of estimation errors around µ (p. 14), which fluctuate in both directions; applying ℝ^n_+ to E would force d ≥ µ on all of U. Every set admitted by the literal reading is admitted here, so the statement covers the source's
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §2.3, remark after Definition 2.2 (unnumbered), p. 15

import Mathlib
import Definitions.Def_FlexMargin_IsPartwiseSymm
import Definitions.Def_FlexMargin_IsPartwiseSymmAround

namespace FlexMargin

/-- **Remark after Definition 2.2: Definition 2.1 sets are Definition 2.2 sets with a constant centre.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §2.3, remark after Definition 2.2 (unnumbered), p. 15: "It is worth pointing out that the
uncertainty sets considered in Definition 2.2 are more general than that in Definition 2.1, since U is
independently symmetric if and only if U is independently symmetric around some µ with µi = µj for all
1 ≤ i,j ≤ n."

For any categories `cat` and any set `U` of demand vectors: `U` is part-wise independently symmetric
(`FlexMargin.IsPartwiseSymm`) if and only if there is a constant `c` such that `U` is part-wise
independently symmetric around the constant vector `μ ≡ c` (`FlexMargin.IsPartwiseSymmAround`).

**Formalization Note.** Both directions are stated; "independently symmetric" is the page's short
form of "part-wise independently symmetric". -/
theorem remark_def21_def22 {n T : ℕ} (cat : Fin n → Fin T) (U : Set (Fin n → ℝ)) :
    IsPartwiseSymm cat U ↔ ∃ c : ℝ, IsPartwiseSymmAround cat (fun _ => c) U := by sorry

end FlexMargin
