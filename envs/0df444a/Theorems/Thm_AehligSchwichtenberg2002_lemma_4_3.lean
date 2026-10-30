-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002_lemma_4_3
-- name    : AehligSchwichtenberg2002.lemma_4_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:56:53.428115+00:00
-- url     : https://prove2.me/theorems/870822b8-2c65-4745-a6b0-a99fd5dd1e39
-- title:
--   Lemma 4.3: Non-Size-Increasing Valuation Under Reduction
-- statement:
--   If `r ↦ r'` at iteration depth `≤ d`, then `|r'|_ξ ≤ |r|_ξ` for every compatible environment `ξ`.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Lemma 4.3, p. 395.

import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

theorem lemma_4_3 {Γ : Context} {t : Term}
    (ht : HasType Γ t .diamond) :
    Γ ≠ [] ∧ freeVars t ≠ [] := by sorry

end AehligSchwichtenberg2002
