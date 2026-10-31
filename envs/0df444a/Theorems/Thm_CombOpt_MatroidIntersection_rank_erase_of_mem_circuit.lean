-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersection_rank_erase_of_mem_circuit
-- name    : CombOpt.MatroidIntersection.rank_erase_of_mem_circuit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:24.201028+00:00
-- url     : https://prove2.me/theorems/d2784b6b-dc13-4d68-a9ce-2d9733e3cc14
-- title:
--   Lemma 8.16 — removing a circuit element from $A\supseteq C$ keeps the rank
-- statement:
--   Let $M=(S,\mathcal I)$ be a matroid with rank function $r$, and let $e\in C\subseteq A$, where $C$ is a circuit of $M$. Then
--   $$r(A\setminus\{e\})=r(A).$$
--
--   Here a **circuit** is a minimal dependent set. This lemma is used repeatedly in the proof of part (b) of the Augmenting Path Theorem (Theorem 8.15).
--
--   **Formalization Note** Circuits are the published `EdmondsPartition.Main.IsCircuit` (dependent, every proper subset independent).
--
--   Differences from the source:
--   - encoding: matroids on a finite set S (a finite set with a family of independent subsets satisfying (M0)-(M2)) → a finite type S (the whole type is the ground set) and a structure Matroid S holding the family Indep : Finset S → Prop and a proof of (M0)-(M2); reason: the same matroids: subsets of S are Finsets of the type, and the axioms are the book's
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Lemma 8.16, p. 292 (PDF p. 299)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_Matroid
import Definitions.Def_CombOpt_MatroidIntersection_rank
import Definitions.Def_EdmondsPartition_Main_Basic

namespace CombOpt.MatroidIntersection

/-- **Lemma 8.16: deleting an element of a circuit inside `A` does not change the rank of `A`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Lemma 8.16, p. 292 (PDF p. 299): "Let M = (S, I) be a matroid with rank function r, and let
e ∈ C ⊆ A, where C is a circuit of M. Then r(A\{e}) = r(A)."

If `C` is a circuit of the matroid `M`, `e ∈ C` and `C ⊆ A`, then `r(A \ {e}) = r(A)`.
A circuit is a minimal dependent set (§8.2, p. 282: "A *circuit* of an independence system
(S, I) is a minimal dependent set"), formalized by the published `EdmondsPartition.Main.IsCircuit`:
`C` is not independent and every proper subset of `C` is independent. -/
theorem rank_erase_of_mem_circuit {S : Type*} [Fintype S] [DecidableEq S] (M : Matroid S)
    (e : S) (C A : Finset S) (hC : EdmondsPartition.Main.IsCircuit M.Indep C) (heC : e ∈ C) (hCA : C ⊆ A) :
    rank M.Indep (A.erase e) = rank M.Indep A := by sorry

end CombOpt.MatroidIntersection
