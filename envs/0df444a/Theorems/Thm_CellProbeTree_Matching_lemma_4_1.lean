-- Prove2me | Theorems.Thm_CellProbeTree_Matching_lemma_4_1
-- name    : CellProbeTree.Matching.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:35:43.595195+00:00
-- url     : https://prove2.me/theorems/c18a85aa-c279-46e2-a6ab-9b4660514723
-- title:
--   Lemma 4.1 — the LR block's terminal gap is after position $c_{\mathrm{piv}} = 2a + 3u$, and the construction is injective
-- statement:
--   Fix integers $u \ge 1$ and $a, b \ge 0$, as in (29). For forests $A_1,\dots,A_u$ of total node size $a$, $B_1,\dots,B_u$ of total node size $b$, and a word $\sigma$ with $u$ letters $R$ and $u$ letters $L$, build the LR block word by (30). Then the terminal empty child occurs at the gap immediately after position
--   $$c_{\mathrm{piv}} = 2a + 3u .$$
--   Given the final word and this fixed gap, one can recover both forests and $\sigma$: two inputs with the same parameters $u, a, b$ and the same block word are equal. Thus the construction is injective.
--
--   Differences from the source:
--   - encoding: "the terminal empty child occurs at the gap immediately after position $c_{\mathrm{piv}}$" → the part of the word that `spine` places before the terminal $D = \varepsilon$ has length $2a + 3u$; reason: the construction inserts the terminal empty word at that gap.
--   - encoding: "given the final word and this fixed gap, one can recover both forests and $\sigma$" → equal block words with the same $(u, a, b)$ (hence the same gap) force equal forests and equal $\sigma$; reason: recovery from the word and the fixed gap is injectivity on the family with fixed parameters.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 18, Lemma 4.1

import Mathlib
import Definitions.Def_CellProbeTree_Matching_LRBlock

namespace CellProbeTree.Matching

/-- Lemma 4.1 (fixed pivot and injectivity): in an LR block (29) with `u ≥ 1`, forests of total
sizes `a`, `b` and an interleaving word with `u` letters of each kind, the terminal empty child
sits in the gap right after position `c_piv = 2a + 3u`; and the block word determines both forests
and the interleaving word, so the construction is injective. -/
theorem lemma_4_1 (u a b : ℕ) (hu : 1 ≤ u) :
    (∀ A B : Fin u → BinaryTree Unit, ∀ σ : Fin (2 * u) → Bool,
        forestSize A = a → forestSize B = b → σ ∈ sigmaWords u →
          (blockPre u A B σ).length = 2 * a + 3 * u) ∧
      (∀ A B A' B' : Fin u → BinaryTree Unit, ∀ σ σ' : Fin (2 * u) → Bool,
        forestSize A = a → forestSize B = b → σ ∈ sigmaWords u →
        forestSize A' = a → forestSize B' = b → σ' ∈ sigmaWords u →
          blockWord u A B σ = blockWord u A' B' σ' → A = A' ∧ B = B' ∧ σ = σ') := by sorry

end CellProbeTree.Matching
