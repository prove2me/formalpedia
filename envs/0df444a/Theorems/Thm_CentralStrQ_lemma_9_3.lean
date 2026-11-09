-- Prove2me | Theorems.Thm_CentralStrQ_lemma_9_3
-- name    : CentralStrQ.lemma_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:26.201984+00:00
-- url     : https://prove2.me/theorems/f060c2d2-7e04-419c-9315-46ec87ae9ed0
-- title:
--   Lemma 9.3 — $\mathrm{PLCP}_T[j]\ge\mathrm{PLCP}_T[j-1]-1$
-- statement:
--   Let $T\in\Sigma^n$ be a string over a linearly ordered alphabet and $j\in[2\,.\,.\,n]$. Then
--   $$
--   \mathrm{PLCP}_T[j]\ \ge\ \mathrm{PLCP}_T[j-1]-1 .
--   $$
--
--   This is the classical property of Sadakane and of Kärkkäinen, Manzini and Puglisi: deleting the first symbol of a suffix and of its predecessor shortens their common prefix by at most one. It is what makes the PLCP bitvector well defined (Lemma 9.4).
--
--   Differences from the source:
--   - encoding: PLCP_T[j] ≥ PLCP_T[j−1] − 1 (integers) → PLCP_T[j−1] ≤ PLCP_T[j] + 1 (naturals); reason: equivalent; avoids natural subtraction
--   - encoding: strings in Σⁿ with 1-based positions → lists over a linearly ordered type, 1-based access; reason: a Lean convention; same instances
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Lemma 9.3, p.163 (PDF p.164)

import Mathlib
import Definitions.Def_CentralStrQ_Strings

set_option autoImplicit false

namespace CentralStrQ

/-- Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*, STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Lemma 9.3, p.163 (PDF p.164): "For every string T ∈ Σⁿ and every j ∈ [2..n], it holds
PLCP_T[j] ≥ PLCP_T[j−1] − 1."

**Formalization Note.** Positions are 1-based; the inequality is written
`PLCP_T[j−1] ≤ PLCP_T[j] + 1` to avoid natural-number subtraction (same content). -/
theorem lemma_9_3 {α : Type} [LinearOrder α] (T : List α) (j : ℕ) (hj : 2 ≤ j)
    (hjn : j ≤ T.length) : PLCP T (j - 1) ≤ PLCP T j + 1 := by sorry

end CentralStrQ
