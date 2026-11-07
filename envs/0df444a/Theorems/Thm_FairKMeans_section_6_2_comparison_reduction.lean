-- Prove2me | Theorems.Thm_FairKMeans_section_6_2_comparison_reduction
-- name    : FairKMeans.section_6_2_comparison_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:42.720264+00:00
-- url     : https://prove2.me/theorems/4078ce4f-c48f-4b99-99c9-147c7ec13e72
-- title:
--   Section 6.2 — every fair solution yields a comparison solution with no more centers and no larger cost
-- statement:
--   Let $(S,\phi_S)$ be a family of centers with an $(\alpha,\beta)$-fair fractional assignment. Then there is a comparison solution $(S^\circ,\phi^\circ)$ (every center at the weighted centroid of its points, (31)) with $|S^\circ|\le|S|$ and
--
--   $$\mathrm{Cost}(P,S^\circ,\phi^\circ)\le\mathrm{Cost}(P,S,\phi_S).$$
--
--   This lets the analysis compare with comparison solutions only; applied to near-optimal fair solutions it reaches $\mathrm{OPT}_{\mathrm{frac}}$.
--
--   Differences from the source:
--   - encoding: comparison solution: s = Σ_p ϕ°(p,s)p / Σ_p ϕ°(p,s) (31) → every column weight positive and S° j = π(j); reason: (31) is defined only for nonzero columns; the reduction deletes zero columns
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Section 6.2, unnumbered reduction, pp.27–28 (PDF pp.29–30)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_Comparison

namespace FairKMeans

/-- **Section 6.2, comparison-solution reduction**, pp.27–28 (PDF 29–30). Cheng–Mo–Song–Ding,
arXiv:2609.07974 (held version, sha256 73e9312c…).

Every fair (fractional) solution `(S, φ_S)` can be turned into a comparison solution
`(S°, φ°)` with no more centers and no larger cost. -/
theorem section_6_2_comparison_reduction {d n m s : ℕ} (I : Instance d n m) (S : Fin s → E d)
    (φ : Fin n → Fin s → ℝ) (hA : IsAssignment φ) (hF : IsFair I φ) :
    ∃ s₀ ≤ s, ∃ (S₀ : Fin s₀ → E d) (φ₀ : Fin n → Fin s₀ → ℝ),
      IsComparison I S₀ φ₀ ∧ cost I S₀ φ₀ ≤ cost I S φ := by sorry

end FairKMeans
