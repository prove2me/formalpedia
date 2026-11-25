-- Prove2me | Theorems.Thm_DynLZ77_Main_lemma_2_2
-- name    : DynLZ77.Main.lemma_2_2
-- status  : Open
-- author  : @shaygo
-- created : 2026-11-25T09:02:57.38355+00:00
-- url     : https://prove2.me/theorems/face1053-f440-5499-a042-93d0cf6779a4
-- title:
--   Lemma 2.2 — $\sum_{i\in I}|\mathrm{DExt}_I(i,S)| = O(|I|\log^2 n)$ ([BGK25, Lemma 17])
-- statement:
--   There is a universal constant $C$ such that for every string $S$ of length $n$ over any alphabet and every set of indices $I\subseteq[1..n]$,
--   $$
--   \sum_{i\in I}\bigl|\mathrm{DExt}_I(i,S)\bigr|\;\le\;C\,|I|\,(1+\log_2 n)^2 ,
--   $$
--   where $\mathrm{DExt}_I(i,S)$ is the set of non-dominated extension points $p_{i,j,S}=(\mathrm{LCS}_S(i,j),\mathrm{LCP}_S(i,j))$, $j\in I$, $j<i$ (definition `DynLZ77_Main_ExtensionPoints`).
--
--   The trivial bound is $O(|I|^2)$. This lemma is the counting tool in the proof of Lemma 1.2: irreducible LPF′ positions are mapped injectively to non-dominated extension points of a synchronizing set (for $\mathrm{Ired}_{\mathrm{Aper}}$) or of the Lyndon positions of runs (for $\mathrm{Ired}_{\mathrm{Per}}$).
--
--   **Formalization Note.** $O(|I|\log^2 n)$ is written as $C\,|I|\,(1+\log_2 n)^2$ with $C$ fixed before the alphabet, $S$ and $I$; the $+1$ keeps the bound meaningful for $n\le 1$ and changes nothing for $n\ge 2$.
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1131.pdf), p. 49 (PDF 51), Lemma 2.2, citing [BGK25, Lemma 17] = Boneh, Golan, Kraus, The Complexity of Dynamic LZ77 is Θ̃(n^{2/3}), SODA 2026, arXiv:2502.12000 (v3), Lemma 4.15

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_DynLZ77_Main_ExtensionPoints

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Lemma 2.2** ([BGK25, Lemma 17]; arXiv:2502.12000 v3, Lemma 4.15). There is a universal
constant `C` such that for every string `S` of length `n` and every `I ⊆ [1..n]`,
`∑_{i∈I} |DExt_I(i,S)| ≤ C·|I|·(1 + log₂ n)²`. -/
theorem lemma_2_2 : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (S : List α) (I : Finset ℕ),
    I ⊆ Finset.Icc 1 S.length →
      ((∑ i ∈ I, (dext S I i).card : ℕ) : ℝ) ≤
        C * (I.card : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := by sorry

end DynLZ77.Main
