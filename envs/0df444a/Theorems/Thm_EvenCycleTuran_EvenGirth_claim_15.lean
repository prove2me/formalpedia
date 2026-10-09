-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_claim_15
-- name    : EvenCycleTuran.EvenGirth.claim_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:29.195926+00:00
-- url     : https://prove2.me/theorems/301de71d-4803-4ad0-bef5-f42e97444fe9
-- title:
--   Claim 15, p. 23 — Σ_{b ≠ a} f_l(a, b) = O(n) for every vertex a of a graph with no cycle of length 3, …, 2l−1 or 2k
-- statement:
--   Let $k>l\ge2$. There is a constant $C$, depending only on $k$ and $l$, such that for every $n$, every graph $G$ on $n$ vertices containing no cycle of length $3,4,\dots,2l-1$ and no cycle of length $2k$, and every vertex $a$ of $G$,
--
--   $$\sum_{b\in V(G)\setminus\{a\}} f_l(a,b)\le C\,n,$$
--
--   where $f_l(a,b)$ is the number of paths of $l$ edges between $a$ and $b$.
--
--   In the proof of Theorem 14 for $m\ge3$ this bounds each factor of the product $\prod_j f_l(v_j,v_{j+1})$ by $O(n)$.
--
--   **Formalization Note.** $O(n)$ is encoded with a constant chosen before $n$, $G$ and $a$. The paper's standing hypothesis at this point reads "does not contain $C_3, C_4, \dots, C_{2l-2}, C_{2k}$", but its proof uses that no layer $N_i(a)$, $i<l$, spans an edge, which needs $C_{2l-1}$ excluded as well; the family of Theorem 14 is used. The proof (Lemma 27 with $p=2k-2l+2$) gives $C=2k-2l+2$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 23, Claim 15 (standing hypothesis p. 22, last paragraph)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem claim_15 (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l - 1) ∪ {2 * k}) G → ∀ a : Fin n,
        (∑ b ∈ univ.erase a, (pathCount G l a b : ℝ)) ≤ C * n := by sorry

end EvenCycleTuran.EvenGirth
