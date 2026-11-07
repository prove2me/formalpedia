-- Prove2me | Theorems.Thm_BalancedKneser_lemma_4_2
-- name    : BalancedKneser.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:53.385913+00:00
-- url     : https://prove2.me/theorems/02db8cae-a953-4e6e-9400-faedc9d2f11a
-- title:
--   Lemma 4.2 (The rook configuration loses a color)
-- statement:
--   Let $D$ be the set of cells of a $3\times3$ array numbered $1,\dots,9$ row by row, and let $A_i$ be the four other cells in the row or column of $i$. Let $\varphi:\binom D4\to[9]$ color the four-subsets of $D$. For a four-set $Z\subseteq D$ put
--   $$
--   B_2(Z)=\Big\{A\in\tbinom D4:\ |A\cap Z|\ge2\Big\}.
--   $$
--   If, for every four-set $Z$, some color of $[9]$ is not taken by $\varphi$ on $B_2(Z)$, then the nine labels $A_1,\dots,A_9$ are not rainbow: two of them receive the same color.
--
--   This is the local coloring step of the ten-color bound: in a proper nine-coloring of $G_{n,3}$ every rook configuration repeats a color.
--
--   **Formalization Note** $D=\mathrm{Fin}\,9$, cell $i$ in row $\lfloor i/3\rfloor$ and column $i\bmod 3$ (the source's cell $i+1$); colors $\mathrm{Fin}\,9$.
--
--   Differences from the source:
--   - encoding: cells 1, …, 9 of the 3 × 3 array, colors [9] → Fin 9 (cell i is the source's cell i + 1, row i / 3, column i % 3), colors Fin 9; reason: relabelling; same statement
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Lemma 4.2, p.9 (PDF p.11); proof §8, pp.14–16 (PDF pp.16–18)

import Mathlib
import Definitions.Def_BalancedKneser_KG
import Definitions.Def_BalancedKneser_rookLabelSets

namespace BalancedKneser

/-- **Lemma 4.2 (The rook configuration loses a color)** (Alipour–Jafari, arXiv:2611.04486v1,
p.9 (PDF p.11); proof §8, pp.14–16): "Let φ : (D 4) → [9]. If each ball
B2(Z) = {A ∈ (D 4) : |A ∩ Z| ≥ 2} misses a color, then the nine labels Aᵢ are not rainbow."

Here `D = Fin 9` is the 3 × 3 array (cell `i` in row `i / 3`, column `i % 3`), `Aᵢ = rookA i`
is the set of the four other cells in the row or column of `i`, `(D 4)` is the set of 4-subsets
of `D`, the colors are `[9] = Fin 9`, and the centers `Z` range over all 4-subsets of `D`.

Formalization Note: the source numbers the cells `1, …, 9` row by row; cell `i : Fin 9` is the
source's cell `i + 1`. -/
theorem lemma_4_2 (φ : KSet 9 4 → Fin 9)
    (hball : ∀ Z : KSet 9 4, ∃ col : Fin 9, ∀ A : KSet 9 4, 2 ≤ (A.1 ∩ Z.1).card → φ A ≠ col) :
    ¬ Function.Injective (fun i : Fin 9 => φ ⟨rookA i, rookA_card i⟩) := by sorry

end BalancedKneser
