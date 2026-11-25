-- Prove2me | Theorems.Thm_DynLZ77_Main_lemma_8_5
-- name    : DynLZ77.Main.lemma_8_5
-- status  : Open
-- author  : @shaygo
-- created : 2026-11-25T15:20:19.006376+00:00
-- url     : https://prove2.me/theorems/745130a3-c5b0-4d9a-9ca4-c8c2ef55accb
-- title:
--   Lemma 8.5 — every index lies in $O(\log n)$ highly periodic runs ([BGS24, Lemma 8])
-- statement:
--   Let $S$ be a string of length $n$. A **run** $S[a..b]$ with period $p=\mathrm{per}(S[a..b])$ is a maximal periodic substring: $2p\le b-a+1$, $S[a-1]\ne S[a-1+p]$ and $S[b+1]\ne S[b+1-p]$ (a comparison with a position outside $S$ counts as unequal). The run is **highly periodic** if $b-a+1\ge 3p$. There is a universal constant $C$ such that every index $i$ of $S$ lies in at most
--   $$
--   C\,(1+\log_2 n)
--   $$
--   highly periodic runs.
--
--   In the proof of Lemma 1.2 ("Bounding $\mathrm{Ired}_{\mathrm{Per}}$"), this lemma bounds the set $R_Z$ of the two leftmost Lyndon-root positions of the highly periodic runs that contain a phrase start: $|R_Z|=O(z\log n)$.
--
--   **Formalization Note.** Runs are counted as pairs $(a,b)\in[1..n]^2$ with `IsRun S a b (per (sub S a b))` and `HighlyPeriodic (sub S a b)` (definitions of `DynLZ77_Main_Structure`); the period of a run is determined by $(a,b)$. $O(\log n)$ is written as $C\,(1+\log_2 n)$ with $C$ fixed before the alphabet, $S$ and $i$.
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1131.pdf), §8.1 Highly periodic words, Lyndon roots, Lemma 8.5, p. 49 (PDF 51), citing [BGS24, Lemma 8] = Boneh, Golan, Shur, String 2-Covers with No Length Restrictions, ESA 2024

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

open Classical in
/-- **Lemma 8.5** ([BGS24, Lemma 8]). There is a universal constant `C` such that every position
`i` of a string `S` of length `n` lies in at most `C·(1 + log₂ n)` highly periodic runs, i.e. runs
`S[a..b]` with period `p = per(S[a..b])` and `b − a + 1 ≥ 3p`. -/
theorem lemma_8_5 : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (S : List α) (i : ℕ),
    (((Finset.Icc 1 S.length ×ˢ Finset.Icc 1 S.length).filter (fun r : ℕ × ℕ =>
        IsRun S r.1 r.2 (per (sub S r.1 r.2)) ∧ HighlyPeriodic (sub S r.1 r.2) ∧
          r.1 ≤ i ∧ i ≤ r.2)).card : ℝ) ≤
      C * (1 + Real.logb 2 (S.length : ℝ)) := by sorry

end DynLZ77.Main
