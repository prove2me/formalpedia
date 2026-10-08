-- Prove2me | Theorems.Thm_EdgeTransBiCayley_TwoArc_proposition_3_3
-- name    : EdgeTransBiCayley.TwoArc.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:45.476108+00:00
-- url     : https://prove2.me/theorems/4343ad0f-3313-4f86-81d9-d11fe9ac0aaf
-- title:
--   Proposition 3.3 — normal local arc-transitivity of BiCay(H, ∅, ∅, S); X arc-transitive iff S^α = S⁻¹, else semisymmetric
-- statement:
--   Let $H$ be a finite group, $S \subseteq H$ with $1 \in S$, let $\Gamma = \mathrm{BiCay}(H,\emptyset,\emptyset,S)$ be connected, and write $X = N_{\mathrm{Aut}(\Gamma)}(R(H))$. Let $\mathrm{F} = \{\sigma_{\alpha,g} \mid S^\alpha = g^{-1}S\}$. Then:
--
--   1. $\Gamma$ is normal locally arc-transitive if and only if the neighbourhood $\Gamma(1_0) = \{s_1 : s \in S\}$ is an orbit of $\mathrm{F}$, that is, for all $s,t \in S$ some $\sigma_{\alpha,g} \in \mathrm{F}$ maps $s_1$ to $t_1$.
--
--   Moreover, if $\Gamma$ is normal locally arc-transitive, then:
--
--   2. $X$ is transitive on the arcs of $\Gamma$ if and only if there is $\alpha \in \mathrm{Aut}(H)$ with
--   $$S^\alpha = S^{-1};$$
--   3. $X$ acts semisymmetrically on $\Gamma$ (transitively on edges but not on vertices) if and only if there is no $\alpha \in \mathrm{Aut}(H)$ with $S^\alpha = S^{-1}$.
--
--   Part 2 gives condition (a) of the main theorem.
--
--   **Formalization Note** Every $\sigma_{\alpha,g} \in \mathrm{F}$ maps $\Gamma(1_0)$ into itself, so "is an orbit of $\mathrm{F}$" is equivalent to transitivity of $\mathrm{F}$ on $\{s_1 : s \in S\}$, which is how it is stated. With $R = L = \emptyset$ the condition of $\mathrm{F}$ in (2.2) reduces to $S^\alpha = g^{-1}S$. The hypothesis $1 \in S$ is the paper's normalisation of the bi-Cayley triple (p. 4); the proof uses the arc $(1_0,1_1)$, and the condition $S^\alpha = S^{-1}$ is not invariant under replacing $S$ by a right translate $Sg$, so the statement depends on it.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 5, Proposition 3.3

import Mathlib
import Definitions.Def_EdgeTransBiCayley_TwoArc_Setting
open Pointwise

namespace EdgeTransBiCayley.TwoArc

theorem proposition_3_3 {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hR : D.R = ∅) (hL : D.L = ∅) (hconn : D.graph.Connected)
    (h1 : (1 : H) ∈ D.S) :
    (IsNormalLocallyArcTransitive D ↔
      ∀ s ∈ D.S, ∀ t ∈ D.S, ∃ (α : MulAut H) (g : H), IsF D α g ∧
        sigmaPerm α g (.inr s) = .inr t) ∧
    (IsNormalLocallyArcTransitive D →
      (IsArcTransitiveOn D.graph (normRH D) ↔
        ∃ α : MulAut H, D.S.image α = D.S⁻¹)) ∧
    (IsNormalLocallyArcTransitive D →
      (IsSemisymmetricOn D.graph (normRH D) ↔
        ¬ ∃ α : MulAut H, D.S.image α = D.S⁻¹)) := by sorry

end EdgeTransBiCayley.TwoArc
