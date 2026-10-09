-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_fat_le
-- name    : EvenCycleTuran.EvenGirth.fat_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:36.26734+00:00
-- url     : https://prove2.me/theorems/334721bf-883b-4276-afa1-31fca1b2ca85
-- title:
--   §5.2, p. 21 — in a graph with no cycle of length 3, …, 2l−1 or 2k, the number of fat C₂ₗ's is at most 2k(k−l)/(l−2)·C(n, 2)
-- statement:
--   Let $k>l\ge3$ and let $G$ be a graph on $n$ vertices containing no cycle of length $3,4,\dots,2l-1$ and no cycle of length $2k$. Then the number of fat copies of $C_{2l}$ in $G$ satisfies
--
--   $$\#\{\text{fat } C_{2l}\text{'s in } G\}\le\frac{2k(k-l)}{l-2}\binom{n}{2}.$$
--
--   Together with the bound $\binom{4l^2-1}{2}\binom n2$ on non-fat $C_{2l}$'s this gives $\mathrm{ex}(n,C_{2l},\mathcal C_{2l-1}\cup\{C_{2k}\})=O(n^2)$, the case $m=2$ of Theorem 14 for $l\ge3$.
--
--   **Formalization Note.** The fraction is a real number; $l\ge3$ is needed for $l-2>0$. The paper treats $l=2$ through Theorems 10 and 11 instead.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 21, §5.2, third paragraph ("Then the number of fat C_{2l}'s is at most …"), with Claim 14 ruling out larger multiplicities

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem fat_le {V : Type*} [Fintype V] (G : SimpleGraph V) (k l : ℕ) (hl : 3 ≤ l) (hkl : l < k)
    (hG : EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l - 1) ∪ {2 * k}) G) :
    (fatCycleCount G l : ℝ) ≤
      2 * (k : ℝ) * ((k : ℝ) - l) / ((l : ℝ) - 2) * ((Fintype.card V).choose 2 : ℝ) := by sorry

end EvenCycleTuran.EvenGirth
