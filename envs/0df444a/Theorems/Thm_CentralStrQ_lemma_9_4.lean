-- Prove2me | Theorems.Thm_CentralStrQ_lemma_9_4
-- name    : CentralStrQ.lemma_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:22:22.973197+00:00
-- url     : https://prove2.me/theorems/e4978007-67ad-4bfa-9b17-ce7d7e4b3bb0
-- title:
--   Lemma 9.4 — the PLCP marks $2j+\mathrm{PLCP}_T[j]$ are strictly increasing in $[1..2n]$
-- statement:
--   Let $T\in\Sigma^n$. Then:
--
--   1. the positions $2j+\mathrm{PLCP}_T[j]$, $j=1,\dots,n$, are strictly increasing in $j$;
--   2. they belong to $[1\,.\,.\,2n]$;
--   3. consequently $B^{\mathrm{PLCP}}_T$ contains exactly $n$ ones;
--   4. for every $j\in[1\,.\,.\,n]$,
--   $$
--   \mathrm{select}_{B^{\mathrm{PLCP}}_T}(j,1)=2j+\mathrm{PLCP}_T[j].
--   $$
--
--   The bitvector therefore represents the PLCP array in $2n$ bits, and a select structure on it answers PLCP queries.
--
--   Differences from the source:
--   - encoding: PLCP_T[j] = select(j,1) − 2j → select(j,1) = 2j + PLCP_T[j] in ℕ∪{∞}; reason: equivalent, and states that the j-th one exists
--   - encoding: strings in Σⁿ with 1-based positions → lists over a linearly ordered type, 1-based access; reason: a Lean convention; same instances
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Lemma 9.4, p.164 (PDF p.165)

import Mathlib
import Definitions.Def_CentralStrQ_Strings
import Definitions.Def_CentralStrQ_PLCPBitvector

set_option autoImplicit false

namespace CentralStrQ

/-- Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*, STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Lemma 9.4, p.164 (PDF p.165): "For every string T ∈ Σⁿ, the positions 2j + PLCP_T[j],
where j = 1, …, n, are strictly increasing and belong to [1..2n]. Consequently, B^PLCP_T is well
defined, contains exactly n ones, and satisfies PLCP_T[j] = select_{B^PLCP_T}(j, 1) − 2j for every
j ∈ [1..n]."

**Formalization Note.** The last clause is written `select(j, 1) = 2j + PLCP_T[j]` in `ℕ∞`, which
also states that the `j`-th one exists. `n = 0` is allowed (all clauses are then trivial). -/
theorem lemma_9_4 {α : Type} [LinearOrder α] (T : List α) :
    (∀ j j' : ℕ, 1 ≤ j → j < j' → j' ≤ T.length → 2 * j + PLCP T j < 2 * j' + PLCP T j') ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ T.length → 1 ≤ 2 * j + PLCP T j ∧ 2 * j + PLCP T j ≤ 2 * T.length) ∧
    (plcpBits T).count true = T.length ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ T.length →
      select (plcpBits T) j true = ((2 * j + PLCP T j : ℕ) : ℕ∞) := by sorry

end CentralStrQ
