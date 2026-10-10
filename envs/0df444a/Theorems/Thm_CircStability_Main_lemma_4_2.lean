-- Prove2me | Theorems.Thm_CircStability_Main_lemma_4_2
-- name    : CircStability.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:35.695412+00:00
-- url     : https://prove2.me/theorems/5cae79bc-58d9-4765-ab44-0e9e7b384055
-- title:
--   Lemma 4.2 — a Hamiltonian (c+1)-closed non-Hamiltonian-connected G_c with many edges and ⌊c/2⌋−1 vertices of degree ≤ ⌊c/2⌋ is W_{c,⌊c/2⌋,c}
-- statement:
--   Let $G_c$ be a Hamiltonian graph on $c\ge6$ vertices. Suppose $G_c$ is $(c+1)$-closed, is not Hamiltonian-connected, and $e(G_c)>h(c+1,\lfloor c/2\rfloor-1)$. If $G_c$ has $\lfloor c/2\rfloor-1$ vertices of degree at most $\lfloor c/2\rfloor$, then
--
--   $$
--   G_c\cong W_{c,\lfloor c/2\rfloor,c}.
--   $$
--
--   This settles the first case of Lemma 2.11 (with $p=1$) in the proof of Theorem 4.1.
--
--   **Formalization Note.** "$G_c=W_{c,\lfloor c/2\rfloor,c}$" is read as a graph isomorphism, not a containment. Hamiltonian is Mathlib's `SimpleGraph.IsHamiltonian` (a cycle through every vertex). The graph is on an arbitrary finite vertex type of size $c$, so the lemma applies directly to $\overline G[C]$.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 17, Lemma 4.2 (proof §4.2, pp. 18–21)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem lemma_4_2 {V : Type*} [Fintype V] [DecidableEq V] (c : ℕ) (hV : Fintype.card V = c)
    (hc : 6 ≤ c) (Gc : SimpleGraph V) [DecidableRel Gc.Adj] (hHam : Gc.IsHamiltonian)
    (hcl : IsKClosed (c + 1) Gc) (hH : ¬ HamConnected Gc)
    (hE : hNum (c + 1) (c / 2 - 1) < #Gc.edgeFinset)
    (hT : ∃ T : Finset V, #T = c / 2 - 1 ∧ ∀ v ∈ T, Gc.degree v ≤ c / 2) :
    Nonempty (Gc ≃g wGraph c (c / 2) c) := by sorry

end CircStability.Main
