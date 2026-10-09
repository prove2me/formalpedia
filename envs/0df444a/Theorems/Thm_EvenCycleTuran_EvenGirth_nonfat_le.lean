-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_nonfat_le
-- name    : EvenCycleTuran.EvenGirth.nonfat_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:31.299906+00:00
-- url     : https://prove2.me/theorems/e0b31ea3-cf60-42c5-93ef-b19d5991632b
-- title:
--   §5.2, p. 21 — the number of non-fat C₂ₗ's is at most C(4l²−1, 2)·C(n, 2)
-- statement:
--   Let $l\ge2$ and let $G$ be a graph on $n$ vertices with girth at least $2l$. A copy of $C_{2l}$ in $G$ is fat if all its $l$ pairs of opposite vertices are fat (joined by at least $4l^2$ paths of length $l$). The number of copies of $C_{2l}$ in $G$ that are not fat satisfies
--
--   $$\#\{\text{non-fat } C_{2l}\text{'s in } G\}\le\binom{4l^2-1}{2}\binom{n}{2}.$$
--
--   Together with the bound on fat $C_{2l}$'s this gives the upper bound of Theorem 14 for $m=2$.
--
--   **Formalization Note.** Girth at least $2l$ is the standing hypothesis of §5.2. The two binomials are natural-number binomials, and $4l^2-1$ is a natural-number subtraction, nonnegative for $l\ge1$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 21, §5.2, first paragraph ("Observe now that the number of non-fat C_{2l}'s is at most …")

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem nonfat_le {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ) (hl : 2 ≤ l)
    (hG : EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l - 1)) G) :
    nonFatCycleCount G l ≤ (4 * l ^ 2 - 1).choose 2 * (Fintype.card V).choose 2 := by sorry

end EvenCycleTuran.EvenGirth
