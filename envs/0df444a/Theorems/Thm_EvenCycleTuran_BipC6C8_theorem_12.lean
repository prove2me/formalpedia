-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_theorem_12
-- name    : EvenCycleTuran.BipC6C8.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:28.990012+00:00
-- url     : https://prove2.me/theorems/b26af09f-5466-4939-ac34-7e5cb1017330
-- title:
--   Theorem 12 — ex_bip(n, C₆, C₈) = n³ + O(n^{5/2})
-- statement:
--   Let $\mathrm{ex}_{bip}(n,C_6,C_8)$ denote the maximum number of $6$-cycles in a bipartite graph on $n$ vertices that contains no cycle of length $8$. Then
--   $$\mathrm{ex}_{bip}(n,C_6,C_8)=n^3+O\bigl(n^{5/2}\bigr)\qquad(n\to\infty),$$
--   that is, there are constants $C$ and $N$ such that $\bigl|\mathrm{ex}_{bip}(n,C_6,C_8)-n^3\bigr|\le C\,n^{5/2}$ for all $n\ge N$.
--
--   This determines the asymptotics of the bipartite generalized Turán number for $C_6$ and $C_8$; the extremal construction is $K_{3,n-3}$. The non-bipartite question $\mathrm{ex}(n,C_6,C_8)$ is left open in the paper.
--
--   **Formalization Note** The statement is two-sided (Mathlib's `IsBigO` of the difference). Copies are unlabelled (`copyCount`); bipartite means `Colorable 2`; $\mathrm{ex}_{bip}$ is a maximum over a nonempty finite set of values.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 6, §2.1, Theorem 12 (proof in §4.2, pp. 14–18)

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem theorem_12 :
    (fun n : ℕ => (exBip n (cycleGraph 6) {8} : ℝ) - (n : ℝ) ^ 3) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((5 : ℝ) / 2)) := by sorry

end EvenCycleTuran.BipC6C8
