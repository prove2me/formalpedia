-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthEven_deletion_step
-- name    : EvenCycleTuran.OddGirthEven.deletion_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:26.291454+00:00
-- url     : https://prove2.me/theorems/e4948cf5-d756-47f6-b02e-80992333b3fa
-- title:
--   §6.2 — every nonempty forbidden-cycle graph has a low-cycle vertex
-- statement:
--   Fix integers $k>l\ge2$. There is a constant $D>0$, depending only on $k,l$, such that for every $n$ and every nonempty graph $G$ on at most $n$ vertices with no cycles of lengths $3,\ldots,2l$ or $2k$, some vertex $v$ belongs to at most
--
--   $$D n^{l/(l+1)}$$
--
--   copies of $C_{2l+1}$. This is the degeneracy conclusion used by the vertex-deletion argument to give the upper bound of Theorem 17.
--
--   **Formalization Note** The ambient bound $n$ is retained while vertices are deleted. The page uses $4c^{l+1}$ in its threshold but mixes $c^l$, $c^{l+1}$ and $4c^{l+1}$ internally; the existential $D$ records the constant needed for this conclusion, chosen before both $n$ and $G$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 28, §6.2, vertex-deletion argument of Theorem 17

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthEven_Setting

namespace EvenCycleTuran.OddGirthEven

/-- The vertex-deletion conclusion in the proof of Theorem 17, p. 28. -/
theorem deletion_step (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k) :
    ∃ D : ℝ, 0 < D ∧ ∀ (n m : ℕ), 0 < m → m ≤ n →
      ∀ G : SimpleGraph (Fin m),
        EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l) ∪ {2 * k}) G →
          ∃ v : Fin m, (cyclesAt G l v : ℝ) ≤
            D * (n : ℝ) ^ ((l : ℝ) / ((l : ℝ) + 1)) := by sorry

end EvenCycleTuran.OddGirthEven
