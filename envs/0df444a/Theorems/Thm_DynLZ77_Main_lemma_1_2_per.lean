-- Prove2me | Theorems.Thm_DynLZ77_Main_lemma_1_2_per
-- name    : DynLZ77.Main.lemma_1_2_per
-- status  : Open
-- author  : @shaygo
-- created : 2026-11-25T09:05:55.977084+00:00
-- url     : https://prove2.me/theorems/c590b792-8b15-5912-b157-718eb1d58f23
-- title:
--   Proof of Lemma 1.2 — the highly periodic part: $|\mathrm{Ired}_{\mathrm{Per}}| = O(z\log^3 n)$
-- statement:
--   For a string $S$ with $z=|\mathrm{LZ77}(S)|$ let
--   $$
--   \mathrm{Ired}_{\mathrm{Per}}=\{\,i\in\mathrm{Ired}_S \mid S[i..i+\mathrm{LPF}'_S(i))\text{ is highly periodic}\,\},
--   $$
--   where a string $X$ is highly periodic if $|X|\ge 3\,\mathrm{per}(X)$. There is a universal constant $C$ such that for every string $S$,
--   $$
--   |\mathrm{Ired}_{\mathrm{Per}}|\;\le\;C\,z\,(1+\log_2|S|)^3 .
--   $$
--
--   This is the second half of the proof of Lemma 1.2 ("Bounding $\mathrm{Ired}_{\mathrm{Per}}$"). The paper maps each $i\in\mathrm{Ired}_{\mathrm{Per}}$ injectively to a non-dominated extension point of the set $R_Z$ of the two leftmost Lyndon-root positions of the highly periodic runs containing a phrase start, using Claims 8.11 and 8.12, Observations 8.6 and 8.7, Lemma 8.5 ($|R_Z|=O(|Z|\log n)$) and Lemma 2.2. Together with the bound on the non-highly-periodic part it gives Lemma 1.2.
--
--   **Formalization Note.** $O(z\log^3 n)$ is written as $C\,z\,(1+\log_2|S|)^3$, as in the mission's statement of Lemma 1.2; `HighlyPeriodic` and `Ired` are those of `DynLZ77_Main_Structure`.
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1131.pdf), proof of Lemma 1.2, "Bounding Ired_Per", pp. 52–53 (PDF 54–55)

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

open Classical in
/-- **Proof of Lemma 1.2, bounding `Ired_Per`** (pp. 52–53). There is a universal constant `C` such
that for every string `S`, the irreducible positions `i` whose equality interval
`S[i..i + LPF′_S(i))` is highly periodic number at most `C·z·(1 + log₂|S|)³`. -/
theorem lemma_1_2_per : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (S : List α),
    (((Ired S).filter (fun i => HighlyPeriodic (sub S i (i + lpf' S i - 1)))).card : ℝ) ≤
      C * (z S : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 3 := by sorry

end DynLZ77.Main
