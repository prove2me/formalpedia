-- Prove2me | Theorems.Thm_FBMSP_theorem1_hardness
-- name    : FBMSP.theorem1_hardness
-- status  : Open
-- author  : @mikeh
-- created : 2026-10-30T04:53:24.518167+00:00
-- url     : https://prove2.me/theorems/3a2ea5dc-ee1e-4414-a416-eeb61139af9e
-- title:
--   Theorem 1 — Hardness with independent mean-zero error
-- statement:
--   There are fixed positive integers $C,d$ such that the following binary-input decision problem is NP-hard under polynomial-time many-one reductions. An input specifies $n$ distinct nonnegative rational predicted values with positive rational probability masses, a common rational finite noise law of mean zero with at most $Cn^d$ listed atoms, a price budget $k\ge1$, and a rational revenue threshold. Decide whether some assignment to $k$ nonnegative real prices reaches the threshold.
--
--   The number of segments is part of the input. Input size is the explicit self-delimiting binary description length. NP verifiers and reductions are finite Turing machines with polynomial transition bounds; an arbitrary computable reduction is insufficient.
--
--   **Review note.** The open reduction proof must verify probability normalization, centering of the common error, and preservation of nonnegative predicted means. The paper's unweighted revenue threshold must be rescaled consistently when customer weights sum to one.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Theorem 1, p.14; reduction pp.39–42 (ec5–ec8).

import Definitions.Def_FBMSP_Hardness

namespace FBMSP

theorem theorem1_hardness :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      NPHard (pricingLanguageWithShockBound C d) := by sorry

end FBMSP
