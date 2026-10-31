-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersection_circuit_unique
-- name    : CombOpt.MatroidIntersection.circuit_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:21.898984+00:00
-- url     : https://prove2.me/theorems/c71f856e-88e9-4eb6-b613-f32ad15c7cb3
-- title:
--   Theorem 8.9 — an independent set plus one element contains at most one circuit
-- statement:
--   Let $M=(S,\mathcal I)$ be a matroid, let $J\in\mathcal I$, and let $e\in S$. Then $J\cup\{e\}$ contains at most one circuit: if $C_1$ and $C_2$ are circuits of $M$ with $C_1,C_2\subseteq J\cup\{e\}$, then $C_1=C_2$.
--
--   This generalizes the fact that adding an edge to a forest creates at most one circuit. It is the basis of the circuit axioms of a matroid and is used in the analysis of the matroid intersection algorithm.
--
--   A **circuit** is a minimal dependent set; a loop $e$ gives the circuit $\{e\}$.
--
--   **Formalization Note** "At most one" is stated as: any two circuits contained in $J\cup\{e\}$ are equal. The case $e\in J$ is included. Circuits are the published `EdmondsPartition.Main.IsCircuit` (dependent, every proper subset independent).
--
--   Differences from the source:
--   - encoding: matroids on a finite set S (a finite set with a family of independent subsets satisfying (M0)-(M2)) → a finite type S (the whole type is the ground set) and a structure Matroid S holding the family Indep : Finset S → Prop and a proof of (M0)-(M2); reason: the same matroids: subsets of S are Finsets of the type, and the axioms are the book's
--   - encoding: J ∪ {e} contains at most one circuit → any two circuits C₁, C₂ ⊆ J ∪ {e} are equal; reason: this is the meaning of 'at most one'
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 8.9, p. 282 (PDF p. 289)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_Matroid
import Definitions.Def_EdmondsPartition_Main_Basic

namespace CombOpt.MatroidIntersection

/-- **Theorem 8.9: an independent set plus one element contains at most one circuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Theorem 8.9, p. 282 (PDF p. 289): "Let (S, I) be a matroid, let J ∈ I, and let e ∈ S. Then
J ∪ {e} contains at most one circuit."

If `J` is independent in the matroid `M`, `e ∈ S`, and `C₁, C₂` are circuits of `M` contained in
`J ∪ {e}`, then `C₁ = C₂`.
A circuit is a minimal dependent set (§8.2, p. 282: "A *circuit* of an independence system
(S, I) is a minimal dependent set"), formalized by the published `EdmondsPartition.Main.IsCircuit`:
`C` is not independent and every proper subset of `C` is independent.

**Formalization Note.** "At most one" is stated as: any two circuits inside `J ∪ {e}` are equal.
`e ∈ J` is allowed (then `J ∪ {e} = J` contains no circuit). -/
theorem circuit_unique {S : Type*} [Fintype S] [DecidableEq S] (M : Matroid S) (J : Finset S)
    (hJ : M.Indep J) (e : S) (C₁ C₂ : Finset S) (hC₁ : EdmondsPartition.Main.IsCircuit M.Indep C₁)
    (hC₂ : EdmondsPartition.Main.IsCircuit M.Indep C₂) (hC₁J : C₁ ⊆ insert e J) (hC₂J : C₂ ⊆ insert e J) :
    C₁ = C₂ := by sorry

end CombOpt.MatroidIntersection
