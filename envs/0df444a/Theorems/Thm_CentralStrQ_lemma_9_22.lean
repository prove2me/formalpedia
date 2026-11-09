-- Prove2me | Theorems.Thm_CentralStrQ_lemma_9_22
-- name    : CentralStrQ.lemma_9_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:22:33.122205+00:00
-- url     : https://prove2.me/theorems/6d4e8653-ab8f-4ada-a043-2de7c8444fb5
-- title:
--   Lemma 9.22 — appending a new smallest symbol: $B^{\mathrm{PLCP}}_{T'}=B^{\mathrm{PLCP}}_T\cdot 01$
-- statement:
--   Let $\sigma\ge 2$, $T\in[0\,.\,.\,\sigma)^n$ and $T'=\mathrm{increase}_1(T)\cdot 0\in[0\,.\,.\,\sigma+1)^{n+1}$, the string obtained by adding one to every symbol and appending a $0$. Then:
--
--   1. $\mathrm{PLCP}_{T'}[j]=\mathrm{PLCP}_T[j]$ for every $j\in[1\,.\,.\,n]$;
--   2. $\mathrm{PLCP}_{T'}[n+1]=0$;
--   3. $B^{\mathrm{PLCP}}_{T'}=B^{\mathrm{PLCP}}_T\cdot 01$.
--
--   It lets the constructions of Section 9, which assume a unique last symbol, be applied to an arbitrary text.
--
--   Differences from the source:
--   - encoding: the bits 0 and 1 → false and true; reason: bitvectors are lists of booleans
--   - encoding: T ∈ [0..σ)ⁿ with 1-based positions → a list of natural numbers, each < σ, 1-based access; reason: a Lean convention; same instances
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Lemma 9.22, p.179 (PDF p.180)

import Mathlib
import Definitions.Def_CentralStrQ_Strings
import Definitions.Def_CentralStrQ_PLCPBitvector

set_option autoImplicit false

namespace CentralStrQ

/-- Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*, STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Lemma 9.22, p.179 (PDF p.180): "Let T ∈ [0..σ)ⁿ, and let T′ = increase₁(T) · 0
(Definition 4.8). Then PLCP_{T′}[j] = PLCP_T[j] for every j ∈ [1..n], and PLCP_{T′}[n + 1] = 0.
Consequently, B^PLCP_{T′} = B^PLCP_T · 01 (Definitions 3.13 and 9.1)."

**Formalization Note.** `T′ = increase 1 T ++ [0]`; the bit `0` is `false`, `1` is `true`.
`n = 0` is allowed. -/
theorem lemma_9_22 (σ : ℕ) (hσ : 2 ≤ σ) (T : List ℕ) (hT : ∀ c ∈ T, c < σ) :
    (∀ j : ℕ, 1 ≤ j → j ≤ T.length → PLCP (increase 1 T ++ [0]) j = PLCP T j) ∧
    PLCP (increase 1 T ++ [0]) (T.length + 1) = 0 ∧
    plcpBits (increase 1 T ++ [0]) = plcpBits T ++ [false, true] := by sorry

end CentralStrQ
