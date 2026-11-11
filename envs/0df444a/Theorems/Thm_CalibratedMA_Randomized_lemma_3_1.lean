-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_lemma_3_1
-- name    : CalibratedMA.Randomized.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:28.018206+00:00
-- url     : https://prove2.me/theorems/e439589d-f12a-444b-8b49-22672b7234e3
-- title:
--   Lemma 3.1 — online residual control for finite tests
-- statement:
--   Let $N\ge1$ and let $\Phi$ be a finite nonempty class of tests $\phi:\mathcal X\times[0,1]\to[-1,1]$, each continuous in its second argument. Run the online rule of Appendix D, which before round $t$ determines a rule $s_t:\mathcal X\to[0,1]$ from the preceding examples, observes $X_t$, predicts $S_t=s_t(X_t)$ and then observes $Y_t$. There is a universal constant $C$ such that for every sequence of examples $(X_t,Y_t)_{t=1}^N$ in $\mathcal X\times[0,1]$,
--   $$\sup_{\phi\in\Phi}\Big|\frac1N\sum_{t=1}^N\phi(X_t,S_t)(Y_t-S_t)\Big|\le C\sqrt{\frac{\log(2|\Phi|)}{N}}.$$
--   The statement also records that $s_t$ takes values in $[0,1]$ and depends only on the examples of rounds before $t$.
--
--   The bound is deterministic and holds against an adversarial sequence. In Theorem 4.1 it controls the empirical residuals of the sequential scores against the tests in $\mathcal G$ and against the lifted class $\mathcal A$.
--
--   **Formalization Note.** The constant is quantified first, `∃ C > 0`, before the input type, $N$, $\Phi$ and the sequence. Rounds are $0,\dots,N-1$, and the tests are only constrained on $\mathcal X\times[0,1]$.
--
--   Differences from the source:
--   - generalization: "There is an online algorithm" → the bound is stated for the specific rule of Appendix D (`onlineRule`), with its online property and range as conclusions; reason: Appendix D proves the lemma for this rule and Algorithm 1 runs this rule; the existence statement follows by taking this rule.
--   - encoding: $\sup_{\phi\in\Phi}|\cdot|\le B$ → $\forall\phi\in\Phi,\ |\cdot|\le B$; reason: equivalent for a finite set.
--   - encoding: rounds $1,\dots,N$ and tests on $\mathcal X\times[0,1]$ → rounds `Fin N` and tests `X → ℝ → ℝ` with hypotheses only on $\mathcal X\times[0,1]$; reason: Lean convention, same instances.
--   - generalization: tests on X × [0,1] → tests extended to X × ℝ, with distinct extensions counted separately even if their restrictions agree; reason: the signed-potential bound applies to this larger family; choosing the clamped extension of each source test recovers its exact cardinality and full bound.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 13, Lemma 3.1 (algorithm and proof: Appendix D, pp. 51–52)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_OnlineRule

universe u

namespace CalibratedMA.Randomized

/-- Lemma 3.1 (p. 13), online residual control for finite tests, for the online rule of
Appendix D: the rule `s_t` depends only on the examples of rounds `< t`, takes values in
`[0,1]`, and for every sequence of examples in `X × [0,1]` every test `ϕ ∈ Φ` has
`|N⁻¹ Σ_t ϕ(X_t, S_t)(Y_t − S_t)| ≤ C √(log(2|Φ|)/N)`, `C` universal. -/
theorem lemma_3_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) (N : ℕ) (Φ : Finset (X → ℝ → ℝ)), 1 ≤ N → Φ.Nonempty →
        (∀ ϕ ∈ Φ, ∀ x, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1)) →
        (∀ ϕ ∈ Φ, ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, ϕ x p ∈ Set.Icc (-1 : ℝ) 1) →
        (∀ (z z' : Fin N → X × ℝ) (t : ℕ), (∀ s : Fin N, (s : ℕ) < t → z s = z' s) →
            onlineRule N Φ z t = onlineRule N Φ z' t) ∧
        (∀ (z : Fin N → X × ℝ) (t : ℕ) (x : X), onlineRule N Φ z t x ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ z : Fin N → X × ℝ, (∀ t, (z t).2 ∈ Set.Icc (0 : ℝ) 1) →
          ∀ ϕ ∈ Φ,
            |(1 / (N : ℝ)) * ∑ t : Fin N,
                ϕ (z t).1 (onlineScore N Φ z t) * ((z t).2 - onlineScore N Φ z t)| ≤
              C * Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / N) := by sorry

end CalibratedMA.Randomized
