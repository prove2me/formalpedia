-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002_lemma_3_5
-- name    : AehligSchwichtenberg2002.lemma_3_5
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:56:32.89892+00:00
-- url     : https://prove2.me/theorems/dcf7735d-0553-4d21-a5c5-211092d5ad01
-- title:
--   Lemma 3.5: Non-Duplicating Reduction Decreases Weight `μ`
-- statement:
--   Every reduction step `r ↦ r'` at iteration depth `d(r) = 0` (without `it`-unfolding or nonlinear `!`-duplication) strictly decreases `μ(r)`.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Lemma 3.5, p. 392.

import Definitions.Def_AehligSchwichtenberg2002_Syntax

namespace AehligSchwichtenberg2002

theorem lemma_3_5 {Γ : Context} {t t' : Term} {τ : Ty}
    (ht : HasType Γ t τ) (hred : RedStep t t') :
    HasType Γ t' τ := by sorry

end AehligSchwichtenberg2002
