-- Prove2me | Theorems.Thm_BeyondConvexity_APTAS_lemma_11
-- name    : BeyondConvexity.APTAS.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:13:00.101228+00:00
-- url     : https://prove2.me/theorems/883f5153-fc27-49f0-9c2e-3f75c3a6cc8b
-- title:
--   Lemma 11 — NFDH square-packing bound
-- statement:
--   Let $S$ be a finite labeled multiset of positive-side axis-aligned squares, with total area $A$ and maximum side $\eta<1$. The specified Next-Fit Decreasing Height algorithm produces a feasible unit-square packing and its bin count satisfies
--
--   $$
--   \operatorname{NFDH}(S)\le\frac{2A+\eta}{1-\eta}+1.
--   $$
--
--   The whole numerator $2A+\eta$ is divided by $1-\eta$. The square sides may be real. The empty input uses $A=\eta=0$ and the algorithm returns zero bins. Occurrence labels are preserved, including for equal side lengths, and boundary contact is allowed. This bound is used in the separator and structured-completion estimates.
--
--   Differences from the source:
--   - encoding: a multiset of squares with maximum side eta → a list of positive real side lengths with maximum computed by folding max from zero; reason: list positions preserve occurrences and ties, and zero fixes the empty-input convention required by the source's applications
--   - encoding: Next-Fit Decreasing Height packs the squares → feasibility and bin count of the explicitly defined shelf algorithm with ties broken by input label; reason: this specifies the algorithm's actual output without changing its choices between unequal sides
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Lemma 11, Appendix B.2, printed p.20 / PDF p.21.

import Definitions.Def_BeyondConvexity_APTAS_nfdh

namespace BeyondConvexity.APTAS

/-- Lemma 11, printed p.20 / PDF p.21. The maximum side is zero on the empty
input, which the actual shelf algorithm packs in zero bins. The entire numerator
2A + η is divided by 1 - η. The sides can be real, not merely rational. -/
theorem lemma_11 (sides : List ℝ)
    (hPositive : ∀ a ∈ sides, 0 < a)
    (hSmall : sides.foldl max 0 < 1) :
    SquarePacking sides (nfdh sides) ∧
      ((nfdh sides).bins : ℝ) ≤
        (2 * (sides.map (fun a => a ^ 2)).sum + sides.foldl max 0) /
          (1 - sides.foldl max 0) + 1 := by sorry

end BeyondConvexity.APTAS
