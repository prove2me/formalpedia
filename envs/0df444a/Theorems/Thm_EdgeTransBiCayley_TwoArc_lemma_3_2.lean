-- Prove2me | Theorems.Thm_EdgeTransBiCayley_TwoArc_lemma_3_2
-- name    : EdgeTransBiCayley.TwoArc.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:35.101405+00:00
-- url     : https://prove2.me/theorems/825c7d26-4f2a-4245-bdeb-65f46f20b56b
-- title:
--   Lemma 3.2 — X_{1₀1₁} = {σ_{α,1} : α ∈ Aut(H, S∖{1})}, and X is not 3-arc-transitive
-- statement:
--   Let $H$ be a finite group, $S \subseteq H$ with $1 \in S$, and let $\Gamma = \mathrm{BiCay}(H,\emptyset,\emptyset,S)$ be connected; write $X = N_{\mathrm{Aut}(\Gamma)}(R(H))$. Then:
--
--   1. the elements of $X$ fixing both vertices $1_0$ and $1_1$ are exactly the automorphisms $\sigma_{\alpha,1} : h_0 \mapsto (h^\alpha)_0,\ h_1 \mapsto (h^\alpha)_1$ with $\alpha \in \mathrm{Aut}(H, S\setminus\{1\})$, the setwise stabiliser of $S \setminus \{1\}$ in $\mathrm{Aut}(H)$:
--   $$X_{1_0 1_1} = \{\sigma_{\alpha,1} \mid \alpha \in \mathrm{Aut}(H, S\setminus\{1\})\};$$
--   2. if $|S| \ge 3$, then $X$ is not transitive on the $3$-arcs of $\Gamma$.
--
--   The first part identifies the two-point stabiliser used in the proof of the main theorem; the second is the "Furthermore" clause of that theorem.
--
--   **Formalization Note** The paper writes $X_{1_01_1} = \langle \sigma_{\alpha,1} \mid \alpha \in \mathrm{Aut}(H,S\setminus\{1\})\rangle$; these permutations already form a group, so the statement is an equivalence for each automorphism $\varphi$ of $\Gamma$. The hypothesis $1 \in S$ is the paper's normalisation of the bi-Cayley triple (p. 4), used when the proof takes $1_1$ as a neighbour of $1_0$. The hypothesis $|S| \ge 3$ on the second part is an addition: for $|S| = 2$ the graph is a cycle of length $2|H|$, whose dihedral automorphism group equals $X$ and is transitive on $3$-arcs, so the printed clause is false there.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 5, Lemma 3.2

import Mathlib
import Definitions.Def_EdgeTransBiCayley_TwoArc_Setting
open Pointwise

namespace EdgeTransBiCayley.TwoArc

theorem lemma_3_2 {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hR : D.R = ∅) (hL : D.L = ∅) (hconn : D.graph.Connected)
    (h1 : (1 : H) ∈ D.S) :
    (∀ φ : D.graph ≃g D.graph,
      (φ ∈ normRH D ∧ φ (.inl 1) = .inl 1 ∧ φ (.inr 1) = .inr 1) ↔
        ∃ α ∈ autStab (D.S.erase 1), ∀ v, φ v = sigmaPerm α 1 v) ∧
    (3 ≤ D.S.card → ¬ IsSArcTransitiveOn D.graph (normRH D) 3) := by sorry

end EdgeTransBiCayley.TwoArc
