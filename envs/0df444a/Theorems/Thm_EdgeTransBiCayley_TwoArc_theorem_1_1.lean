-- Prove2me | Theorems.Thm_EdgeTransBiCayley_TwoArc_theorem_1_1
-- name    : EdgeTransBiCayley.TwoArc.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:39:42.34277+00:00
-- url     : https://prove2.me/theorems/4f017385-5efc-44f6-92bc-2d8b8a59b5de
-- title:
--   Theorem 1.1 — N_Aut(Γ)(R(H)) is 2-arc-transitive on BiCay(H, ∅, ∅, S) iff (a)–(c), and not 3-arc-transitive
-- statement:
--   Let $H$ be a finite group and $S \subseteq H$ with $1 \in S$ and $|S| \ge 2$, and let $\Gamma = \mathrm{BiCay}(H,\emptyset,\emptyset,S)$ be connected: its vertices are $h_0, h_1$ ($h \in H$) and its edges are $\{h_0,(sh)_1\}$ for $h \in H$, $s \in S$. Let $X = N_{\mathrm{Aut}(\Gamma)}(R(H))$ be the normaliser in $\mathrm{Aut}(\Gamma)$ of the group $R(H)$ of right multiplications $h_i \mapsto (hg)_i$. Then $X$ acts transitively on the $2$-arcs of $\Gamma$ if and only if the following three conditions hold:
--
--   1. (a) there is an automorphism $\alpha$ of $H$ with $S^\alpha = S^{-1}$;
--   2. (b) the setwise stabiliser of $S \setminus \{1\}$ in $\mathrm{Aut}(H)$ is transitive on $S\setminus\{1\}$;
--   3. (c) there are $s \in S\setminus\{1\}$ and an automorphism $\beta$ of $H$ with $S^\beta = s^{-1}S$.
--
--   In symbols,
--   $$X \text{ is 2-arc-transitive} \iff \text{(a)} \wedge \text{(b)} \wedge \text{(c)}.$$
--   Furthermore, if $|S| \ge 3$, then $X$ is not transitive on the $3$-arcs of $\Gamma$.
--
--   By Lemma 3.1 every connected normal edge-transitive bi-Cayley graph has this form, so the theorem describes when the normaliser of $R(H)$ is $2$-arc-transitive in general, and shows it is never $3$-arc-transitive. It answers two questions of C. H. Li on bi-normal Cayley graphs.
--
--   **Formalization Note** Three hypotheses are added to the printed statement. (i) $1 \in S$: the paper's normalisation of the bi-Cayley triple (p. 4; Proposition 2.1(b)), on which conditions (b) and (c), phrased with $S \setminus \{1\}$, and the proof (which uses the arc $(1_0,1_1)$) rely. (ii) $|S| \ge 2$: for $|S| = 1$ the graph is a single edge, it has no $2$-arcs, so $2$-arc-transitivity would hold vacuously while (c) fails. (iii) $|S| \ge 3$ on the "Furthermore" clause: for $|S| = 2$ the graph is a cycle of length $2|H|$ and $X$ is its full dihedral automorphism group, which is transitive on $3$-arcs. Condition (b) is stated as: for all $s, t \in S\setminus\{1\}$ there is $\alpha$ with $(S\setminus\{1\})^\alpha = S\setminus\{1\}$ and $s^\alpha = t$. $S^{-1}$ and $s^{-1}S$ are pointwise. Transitivity is for $X$, not for the full $\mathrm{Aut}(\Gamma)$.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 2, Theorem 1.1

import Mathlib
import Definitions.Def_EdgeTransBiCayley_TwoArc_Setting
open Pointwise

namespace EdgeTransBiCayley.TwoArc

theorem theorem_1_1 {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hR : D.R = ∅) (hL : D.L = ∅) (hconn : D.graph.Connected)
    (h1 : (1 : H) ∈ D.S) (h2 : 2 ≤ D.S.card) :
    (IsSArcTransitiveOn D.graph (normRH D) 2 ↔
      (∃ α : MulAut H, D.S.image α = D.S⁻¹) ∧
      (∀ s ∈ D.S.erase 1, ∀ t ∈ D.S.erase 1, ∃ α : MulAut H,
          (D.S.erase 1).image α = D.S.erase 1 ∧ α s = t) ∧
      (∃ s ∈ D.S.erase 1, ∃ β : MulAut H, D.S.image β = s⁻¹ • D.S)) ∧
    (3 ≤ D.S.card → ¬ IsSArcTransitiveOn D.graph (normRH D) 3) := by sorry

end EdgeTransBiCayley.TwoArc
