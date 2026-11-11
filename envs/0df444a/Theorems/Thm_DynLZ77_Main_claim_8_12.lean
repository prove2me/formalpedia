-- Prove2me | Theorems.Thm_DynLZ77_Main_claim_8_12
-- name    : DynLZ77.Main.claim_8_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:21:50.824168+00:00
-- url     : https://prove2.me/theorems/69639ef4-e909-4b42-90b1-2f8c261b57b0
-- title:
--   Claim 8.12 — a highly periodic irreducible $E_i$ starts within $p$ of its run
-- statement:
--   Let $i\in\mathrm{Ired}_S$ and $\ell=\mathrm{LPF}'_S(i)$, and suppose $S[i..i+\ell)$ is highly periodic (i.e. $i\in\mathrm{Ired}_{Per}$); let $p=\mathrm{per}(S[i..i+\ell))$ and let $R=S[a..b]$ be the maximal run with period $p$ containing $S[i..i+\ell)$. Then
--   $$i\le a+p.$$
--   The hypotheses are the context the paper fixes just before the claim, inside the proof of Lemma 1.2 ("Bounding $\mathrm{Ired}_{Per}$").
--
--   Differences from the source:
--   - reading: Ired_S = {1} ∪ {i > 1 | i + LPF′_S(i) ≠ i − 1 + LPF′_S(i − 1)} → Ired S ⊆ [1..|S|]: position 1 belongs to Ired_S only when |S| ≥ 1; reason: Ired_S is a set of positions of S ("irreducible LPF′ positions"); the empty string has no position 1, and with 1 ∈ Ired_ε the statement would be about a non-existent position
--   - reading: R = S[a..b] the maximal run with period p containing S[i..i + ℓ) → IsRun S a b p with a ≤ i and i + ℓ − 1 ≤ b; reason: a run is maximal by definition (p. 15); containment is a ≤ i and i + ℓ − 1 ≤ b
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 53 (PDF 55), Claim 8.12, with its context on pp. 52-53 (PDF 54-55) (proof of Lemma 1.2, §8.2)

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Claim 8.12** (p. 53). Let `i ∈ Ired_S` with `ℓ = LPF′_S(i)` and `S[i..i + ℓ)` highly
periodic, `p = per(S[i..i + ℓ))`, and let `R = S[a..b]` be the maximal run with period `p`
containing `S[i..i + ℓ)`. Then `i ≤ a + p`. -/
theorem claim_8_12 {α : Type} [DecidableEq α] (S : List α) (i : ℕ) (hi : i ∈ Ired S) (ℓ : ℕ)
    (hℓ : ℓ = lpf' S i) (hhp : HighlyPeriodic (sub S i (i + ℓ - 1))) (p : ℕ)
    (hp : p = per (sub S i (i + ℓ - 1))) (a b : ℕ) (hR : IsRun S a b p) (hai : a ≤ i)
    (hib : i + ℓ - 1 ≤ b) :
    i ≤ a + p := by sorry

end DynLZ77.Main
