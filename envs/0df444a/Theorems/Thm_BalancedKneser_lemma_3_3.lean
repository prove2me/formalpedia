-- Prove2me | Theorems.Thm_BalancedKneser_lemma_3_3
-- name    : BalancedKneser.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:11.299216+00:00
-- url     : https://prove2.me/theorems/c4db3c20-ddd3-4782-844a-e4f787908bb1
-- title:
--   Lemma 3.3 (The pentagon loses a color)
-- statement:
--   Let $D$ be a five-point set arranged as a pentagon, and let $A_i$ be the pair of neighbors of point $i$. Let $\varphi:\binom D2\to[5]$ color the ten pairs of $D$. For a pair $Z\subseteq D$ put
--   $$
--   B_1(Z)=\Big\{A\in\tbinom D2:\ A\cap Z\neq\emptyset\Big\}.
--   $$
--   If, for every pair $Z$, some color of $[5]$ is not taken by $\varphi$ on $B_1(Z)$, then the five pentagon labels $A_1,\dots,A_5$ are not rainbow: two of them receive the same color.
--
--   This is the local coloring step of the six-color theorem: in a proper five-coloring of $G_{n,2}$ every pentagon configuration repeats a color, so every pentagon cycle maps to zero under the coloring map.
--
--   **Formalization Note** $D=\mathrm{Fin}\,5$ with $A_i=\{i-1,i+1\}$ (mod 5) and colors $\mathrm{Fin}\,5$; every pentagon on five points is a relabelling of this one.
--
--   Differences from the source:
--   - encoding: a five-point set D with a pentagon, colors [5] → Fin 5 with pentA i = {i + 1, i − 1}, colors Fin 5; reason: the statement is invariant under relabelling D and the colors
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Lemma 3.3, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_BalancedKneser_KG
import Definitions.Def_BalancedKneser_pentagonLabelSets

namespace BalancedKneser

/-- **Lemma 3.3 (The pentagon loses a color)** (Alipour–Jafari, arXiv:2611.04486v1, p.7
(PDF p.9)): "Let φ : (D 2) → [5]. If each ball B1(Z) misses a color, then the five pentagon
labels Aᵢ are not rainbow."

Here `D = Fin 5` with the pentagon `pentA` (the labels `Aᵢ = {i − 1, i + 1}`), `(D 2)` is the
set of pairs of `D`, the colors are `[5] = Fin 5`, and for a pair `Z`,
`B₁(Z) = {A ∈ (D 2) : A ∩ Z ≠ ∅}`; "misses a color" means some color is not a value of `φ` on
`B₁(Z)`. Rainbow means that the labels have distinct colors.

Formalization Note: every five-point set with a pentagon is a relabelling of `Fin 5` with
`pentA`, and the statement is invariant under relabelling. -/
theorem lemma_3_3 (φ : KSet 5 2 → Fin 5)
    (hball : ∀ Z : KSet 5 2, ∃ col : Fin 5, ∀ A : KSet 5 2, (A.1 ∩ Z.1).Nonempty → φ A ≠ col) :
    ¬ Function.Injective (fun i : Fin 5 => φ ⟨pentA i, pentA_card i⟩) := by sorry

end BalancedKneser
