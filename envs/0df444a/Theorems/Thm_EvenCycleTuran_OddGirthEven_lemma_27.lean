-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthEven_lemma_27
-- name    : EvenCycleTuran.OddGirthEven.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:06.237255+00:00
-- url     : https://prove2.me/theorems/0a322a8e-6845-44fa-a668-0c972e2d77a6
-- title:
--   Lemma 27 — a partition with forbidden paths has at most mn edges
-- statement:
--   Let $m\ge1$ and partition the vertices of a finite graph $G$ into $s\ge1$ classes $V_1,\ldots,V_s$. Suppose no path on three vertices has both endpoints in the same class $V_i$ for $i<s$; no path on $m+1$ vertices has endpoints in different classes; and $V_s$ is independent. Then
--
--   $$|E(G)|\le m|V(G)|.$$
--
--   This is the explicit uniform bound established in the proof of Lemma 27. Its independence from the number of classes lets it be used when the partition comes from the neighbours of a vertex.
--
--   **Formalization Note** Classes are fibres of a map to a finite index type and may be empty. Paths have distinct vertices and $m$ edges. The paper states $O(n)$ for fixed $m,s$; its proof gives the displayed $mn$ bound.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 19, Lemma 27 and its proof

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthEven_Setting

namespace EvenCycleTuran.OddGirthEven

/-- Lemma 27, p. 19, with the explicit bound from its proof. -/
theorem lemma_27 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m s : ℕ) (hm : 0 < m) (part : V → Fin (s + 1))
    (hP3 : ∀ a b c : V, a ≠ b → part a = part b →
      part a ≠ Fin.last s → G.Adj a c → G.Adj c b → False)
    (hPath : ∀ p : Fin (m + 1) ↪ V,
      (∀ i : Fin m, G.Adj (p i.castSucc) (p i.succ)) →
      part (p 0) = part (p (Fin.last m)))
    (hIndependent : ∀ a b : V, part a = Fin.last s → part b = Fin.last s →
      ¬ G.Adj a b) :
    (by classical exact G.edgeFinset.card) ≤ m * Fintype.card V := by sorry

end EvenCycleTuran.OddGirthEven
