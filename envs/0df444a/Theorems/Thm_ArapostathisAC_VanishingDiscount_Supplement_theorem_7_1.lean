-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_7_1
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:15:39.765014+00:00
-- url     : https://prove2.me/theorems/e048e18e-aa53-4e7f-8047-025fc5ad366e
-- title:
--   Theorem 7.1 (corrected: $T=\psi$ where $V=0$) — $J^*_\beta$ is concave on the belief simplex, satisfies the DCOE (7.15), and minimizing separated stationary policies are optimal
-- statement:
--   Consider a partially observable model with finite or countably infinite hidden state space $X$ and observation space $Y$, a compact metric (in particular, finite) action space $A$, Assumption 7.1 (transition law $P(x,y\mid x',a)$ and cost $c(x,a)\ge0$ independent of the observation, $U(y)=A$), and $P$, $c$ continuous in $a$. Let $\Delta$ be the belief simplex and $V$, $T$, $\tilde c$ as in (7.11), (7.12), (7.14). For the (DC′) problem and every $0<\beta<1$:
--
--   1. $J^*_\beta$ is concave on $\Delta$;
--   2. the DCOE holds, with the minimum attained:
--   $$J^*_\beta(\psi)=\min_{a\in A}\Big\{\tilde c(\psi,a)+\beta\sum_{y\in Y}V(y,\psi,a)\,J^*_\beta(T(y,\psi,a))\Big\};\tag{7.15}$$
--   3. every nonrandomized separated stationary policy $f:\Delta\to A$ attaining the minimum in (7.15) at every $\psi$ is optimal: $J_\beta(\psi,f)=J^*_\beta(\psi)$ for every $\psi$.
--
--   **Formalization Note** $J^*_\beta$ and the costs are in $[0,\infty]$; the expectation over the belief process is the sum over observation records weighted by their probabilities $\prod_sV(y_s,\Psi_{s-1},A_{s-1})$. Concavity is $t\,J^*_\beta(\psi_1)+(1-t)J^*_\beta(\psi_2)\le J^*_\beta(t\psi_1+(1-t)\psi_2)$ for $t\in[0,1]$.
--
--   Differences from the source:
--   - correction: (7.12) sets T(y, ψ, a) = 0 when V(y, ψ, a) = 0 → T(y, ψ, a) = ψ in that case; reason: 0 is not a belief, so J*_β(T) would be undefined; T enters (7.13) and (7.15) only with the weight V = 0, so any belief gives the same terms; no case is excluded
--   - reading: J*_β of (DC′): the minimum over separated admissible policies → the infimum of J_β(ψ, π) over nonrandomized separated policies, arbitrary functions of the belief history; reason: from a fixed prior only countably many belief histories occur under a nonrandomized policy, so such policies agree there with Borel ones, and for discounted nonnegative costs randomization does not lower the value
--   - reading: A finite or compact → A a nonempty compact metric space; reason: a finite set with the discrete metric is compact metric; U(y) = A is nonempty because U is strict
--   - encoding: beliefs, costs and J*_β as real or extended-real numbers → values in [0, ∞] (lintegrals of the nonnegative cost), compared in EReal where signed terms occur; reason: Lean convention; costs are nonnegative on K (Assumption 2.1), so the instances are the same and infinite values are represented exactly
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 328, Theorem 7.1 and (7.15); pp. 325–328, Assumption 7.1, §7.2.2, (7.9)–(7.14), (DC′)

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Separated

open Filter Topology
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 7.1 (p. 328). For the (DC′) problem of a partially observable model with countable
hidden and observation spaces, compact metric action space and Assumption 7.1, and every
`0 < β < 1`: `J*_β` is concave on the belief simplex `Δ`; it satisfies the DCOE (7.15)
`J*_β(ψ) = min_{a ∈ A} {c̃(ψ, a) + β ∑_y V(y, ψ, a) J*_β(T(y, ψ, a))}`, the minimum being attained;
and every nonrandomized separated stationary policy attaining the minimum in (7.15) at every
belief is optimal. -/
theorem theorem_7_1 {X Y A : Type*} [Countable X] [Countable Y] [MetricSpace A]
    [CompactSpace A] [Nonempty A]
    (M : POModel X Y A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ (ψ₁ ψ₂ ψ : Belief X) (t : ℝ≥0∞), t ≤ 1 →
      (∀ x, ψ.1 x = t * ψ₁.1 x + (1 - t) * ψ₂.1 x) →
      t * sepDiscValue M β ψ₁ + (1 - t) * sepDiscValue M β ψ₂ ≤ sepDiscValue M β ψ) ∧
    (∀ ψ : Belief X, (∃ a : A, sepDiscValue M β ψ = dcoeTerm M β ψ a) ∧
      ∀ a : A, sepDiscValue M β ψ ≤ dcoeTerm M β ψ a) ∧
    (∀ f : Belief X → A, (∀ ψ a, dcoeTerm M β ψ (f ψ) ≤ dcoeTerm M β ψ a) →
      ∀ ψ, sepDiscCost M (fun _ ψ' => f ψ') β ψ = sepDiscValue M β ψ) := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
