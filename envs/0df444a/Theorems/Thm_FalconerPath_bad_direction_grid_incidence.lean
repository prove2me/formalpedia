-- Prove2me | Theorems.Thm_FalconerPath_bad_direction_grid_incidence
-- name    : FalconerPath.bad_direction_grid_incidence
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-05T23:14:49.379372+00:00
-- url     : https://prove2.me/theorems/607d1eb1-a73d-4058-82ef-65a26d887ebf
-- title:
--   Borel grid envelope and incidence lower bound for bad directions
-- statement:
--   Let $k\in\mathbb N$ and $L,C,\delta,q,c\in\mathbb R$ satisfy $L,C,c>0$ and $0<\delta\le1$. Let $\mu$ be a probability on $\mathbb R^{k+1}$ carried by $\overline B(0,L)$. Write $\mathcal T_L(w,b,r)=\{y:\|y\|\le L,\ \operatorname{dist}(y,b+\mathbb Rw)\le r\}$ and let $\mathcal B(\mu,L,C,\delta,q,c)$ be the set of $w\in S^k$ for which some finite anchor set $F\subset\mathbb R^{k+1}$ has $\#F\le\delta^{-q-c}$ and $\mu(\bigcup_{b\in F}\mathcal T_L(w,b,C\delta))\ge\delta^c$. There exist a Borel set $B^+\subseteq S^k$ containing $\mathcal B(\mu,L,C,\delta,q,c)$ and a Borel set $E\subseteq\mathbb R^{k+1}\times S^k$ such that for every $w\in S^k$ there is a finite anchor set $F_w$ with $\#F_w\le\delta^{-q-c}$ and, for every $(x,w)\in E$, some $b\in F_w$ satisfies $\|P_{w^\perp}(x-b)\|\le(C+1)\delta$. For every measure $\nu$ on the sphere with $\nu(S^k)\le1$, $\delta^c\nu(\{w\in S^k:w\in B^+\})\le(\mu\otimes\nu)(E)$. The envelope and incidence are chosen before $\nu$.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf, Section 4, Corollary 4.8 (ang:bad-directions), proof paragraph beginning with the enlarged width, specifically from the fixed bounded spatial delta-grid candidate lists through the first candidate attaining the threshold and its measurable incidence lower bound. A sufficiently fine spatial anchor grid realizes the fixed enlargement as C+1.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
/-- Section 4, proof of Corollary 4.8, from "In a fixed bounded spatial
δ-grid" through "Its measurable incidence relation has mass at least ...".
Finite anchor rounding uses width C+1 (a sufficiently fine spatial grid).
The envelope and the first-candidate incidence are chosen before ANY direction
law; this statement has no direction nonconcentration or incidence gain. -/
theorem bad_direction_grid_incidence {k : ℕ}
    (L C δ q c : ℝ) (hL : 0 < L) (hC : 0 < C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : 0 < c)
    (μ : Measure (Space (k+1))) (hμ : Probability μ)
    (hcar : Carried μ (Metric.closedBall 0 L)) :
    ∃ Bplus : Set (Space (k+1)),
      MeasurableSet Bplus ∧ Bplus ⊆ unitSphere (k+1) ∧
      badDirections μ L C δ q c ⊆ Bplus ∧
      ∃ E : Set (Space (k+1) × Metric.sphere (0 : Space (k+1)) 1),
        MeasurableSet E ∧
        (∀ w : Metric.sphere (0 : Space (k+1)) 1,
          ∃ anchors : Finset (Space (k+1)),
            (anchors.card : ℝ) ≤ δ^(-q-c) ∧
            ∀ x : Space (k+1), (x,w) ∈ E → ∃ a ∈ anchors,
              ‖(ℝ ∙ (w : Space (k+1)))ᗮ.orthogonalProjectionOnto (x-a)‖ ≤ (C+1)*δ) ∧
        ∀ ν : Measure (Metric.sphere (0 : Space (k+1)) 1), ν univ ≤ 1 →
          ENNReal.ofReal (δ^c) * ν (Subtype.val ⁻¹' Bplus) ≤ (μ.prod ν) E := by sorry
end FalconerPath
