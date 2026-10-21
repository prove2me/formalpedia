-- Prove2me | Theorems.Thm_AddictivePlatforms_Compete_lemma_B_4
-- name    : AddictivePlatforms.Compete.lemma_B_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:58:19.783628+00:00
-- url     : https://prove2.me/theorems/66535e2a-bbda-49ea-858e-031ef8c6d419
-- title:
--   Lemma B.4, p. 30 — the incremental gain of joining platform 1 is greater after joining S′ ⊊ S than after S: V(y₂,S) − V(y₁,S) ≤ V(y₂,S′) − V(y₁,S′)
-- statement:
--   Assume Assumptions 1–2 (with the mission's standing pins). Fix a cap $\overline{A}$ and addictiveness $(d_1,\dots,d_K) \in \mathbb{R}^K_+$, and write $K_{-1} = \{2,\dots,K\}$. For $y \in [0,1]$ and $S \subseteq K_{-1}$ let
--   $$V(y,S) := \max_{(a_k)_{k\in S\cup\{1\}}} \; \sum_{k\in S} u(a_k,d_k) + y\cdot u(a_1,d_1) - C\Big(\sum_{k\in S\cup\{1\}} a_k\Big) \quad \text{s.t. } \sum_{k\in S\cup\{1\}} a_k \le \overline{A},\ a_k \ge 0. \qquad (A.4)$$
--   Then for all $S' \subsetneq S \subseteq K_{-1}$ the inequality (A.5), $\partial V/\partial y\,(y,S) \le \partial V/\partial y\,(y,S')$, holds in integrated form:
--   $$V(y_2,S) - V(y_1,S) \le V(y_2,S') - V(y_1,S') \qquad \text{for all } 0 \le y_1 \le y_2 \le 1,$$
--   and in particular
--   $$V(1,S) - V(0,S) \le V(1,S') - V(0,S').$$
--
--   The parameter $y$ interpolates between not using platform 1 ($y = 0$) and joining it ($y = 1$), so $V(1,S) - V(0,S)$ is the consumer's incremental gain of joining platform 1 when she already uses $S$: it shrinks as she joins more platforms. Step 3 of the proof of Proposition 2 uses it to rule out asymmetric equilibria.
--
--   **Formalization Note.** The paper's platform 1 is the index `0`. The lemma's last sentence ("these inequalities are strict whenever the consumer allocates positive attention to every platform in $S$ and $S'$") is **not** posed: with linear $C$ and a large cap (the paper's Figure 3 instance, cf. its footnote 11) the problem separates across platforms, every platform receives positive attention, and both sides are equal. (A.5) is stated in integrated form because $V$ is convex but not necessarily differentiable in $y$. The maximizer is a parameter `a` assumed to solve (A.4) for every $y \in [0,1]$ and $S \subseteq K_{-1}$.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 30, Lemma B.4, (A.4)–(A.5); proof pp. 30–31

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Compete

/-- Lemma B.4 (p. 30), weak part. Fix `(d_1, …, d_K) ∈ ℝ₊^K` and let `a(y, S)` solve (A.4) for every
`y ∈ [0, 1]` and `S ⊆ K₋₁ = K ∖ {1}`, with value `V(y, S)`. For `S′ ⊊ S ⊆ K₋₁`, (A.5) in integrated
form: `V(y₂, S) − V(y₁, S) ≤ V(y₂, S′) − V(y₁, S′)` for `0 ≤ y₁ ≤ y₂ ≤ 1`; in particular
`V(1, S) − V(0, S) ≤ V(1, S′) − V(0, S′)`. Platform "1" is the index `0`. -/
theorem lemma_B_4 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) {K : ℕ} [NeZero K]
    (Abar : ℝ≥0∞) (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k)
    (a : ℝ → Finset (Fin K) → (Fin K → ℝ))
    (ha : ∀ y ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin K), S ⊆ Finset.univ.erase 0 →
      IsB4Max u C Abar d y S (a y S))
    (S S' : Finset (Fin K)) (hSsub : S ⊆ Finset.univ.erase 0) (hS'S : S' ⊂ S) :
    (∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      objB4 u C d y₂ S (a y₂ S) - objB4 u C d y₁ S (a y₁ S) ≤
        objB4 u C d y₂ S' (a y₂ S') - objB4 u C d y₁ S' (a y₁ S')) ∧
    objB4 u C d 1 S (a 1 S) - objB4 u C d 0 S (a 0 S) ≤
      objB4 u C d 1 S' (a 1 S') - objB4 u C d 0 S' (a 0 S') := by sorry

end AddictivePlatforms.Compete
