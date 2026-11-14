-- Prove2me | Theorems.Thm_ConsistentSubmodular_sampleExpectation_lower_tail_le
-- name    : ConsistentSubmodular.sampleExpectation_lower_tail_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:05.978224+00:00
-- url     : https://prove2.me/theorems/f1af8401-ddd2-4266-b632-5c7689bf6389
-- title:
--   Equation (37) — lower tail of a monotone submodular function of an independent sample
-- statement:
--   Let $U$ be a finite set, $p:U\to[0,1]$, and let $S\subseteq U$ contain each $i$ independently with probability $p_i$. Let $G$ be monotone and submodular on finite sets, let $c>0$ with $G(A\cup\{e\})-G(A)\le c$ for all $A,e$, and let $M>0$ with $\mathbb E[G(S)]-G(\emptyset)\le M$. Then for every $a\ge 0$,
--
--   $$\Pr\big[\,G(S)\le \mathbb E[G(S)]-a\,\big]\;\le\;\exp\!\Big(-\frac{a^2}{2cM}\Big).$$
--
--   (The probability is expressed as the expectation of the indicator of the event.) Thus a function with marginals at most $c$ whose mean exceeds its empty value by at most $M$ falls $a$ or more below its mean with probability at most $\exp(-a^2/(2cM))$.
--
--   This is the lower-tail estimate (37) of the paper, used to show that threshold rounding preserves objective values of intersections.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ExponentialTails.lean#L203-L271 (`ConsistentSubmodular.sampleExpectation_lower_tail_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem ConsistentSubmodular.sampleExpectation_lower_tail_le (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (G : Finset ι → ℝ)
    (hmono : ∀ A B, A ⊆ B → G A ≤ G B)
    (hsub : ∀ A B, G (A ∪ B) + G (A ∩ B) ≤ G A + G B)
    {c M a : ℝ} (hc : 0 < c) (hcap : ∀ A e, G (insert e A) - G A ≤ c) (hM : 0 < M)
    (hmean : sampleExpectation U p G - G ∅ ≤ M) (ha : 0 ≤ a) :
    sampleExpectation U p (fun S => if G S ≤ sampleExpectation U p G - a then 1 else 0) ≤
      Real.exp (-(a ^ 2) / (2 * c * M)) := by sorry
