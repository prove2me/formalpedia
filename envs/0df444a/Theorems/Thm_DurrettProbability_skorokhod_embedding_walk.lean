-- Prove2me | Theorems.Thm_DurrettProbability_skorokhod_embedding_walk
-- name    : DurrettProbability.skorokhod_embedding_walk
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-19T02:15:11.969178+00:00
-- url     : https://prove2.me/theorems/e814b5bb-a287-44d3-8b86-695efc79260f
-- title:
--   Theorem 8.1.2 — the whole random walk embedded in a Brownian motion
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb{R}$ with mean zero and variance one:
--   $\int x\,d\mu=0$ and $\int x^2\,d\mu=1$, both integrals absolutely convergent.
--
--   Then there exist a probability space, a Brownian motion $B$ on it, an increasing family $F_t$ of
--   $\sigma$-fields containing the Brownian past $\sigma(B_s:s\le t)$, and times
--   $T_0,T_1,T_2,\dots$ such that
--
--   1. each $T_n$ is a stopping time for $F$, and $T_0=0$ with $T_n\le T_{n+1}$ everywhere;
--   2. the process $n\mapsto B(T_n)$ has the law of the partial-sum process of an i.i.d. sequence
--      with step law $\mu$ — that is, the push-forward of $\omega\mapsto(B(T_n\omega))_{n\ge0}$ on
--      the sequence space $\mathbb{R}^{\mathbb N}$ equals the push-forward of
--      $(x_k)\mapsto\bigl(\sum_{k<n}x_k\bigr)_{n\ge0}$ under the infinite product measure
--      $\mu^{\otimes\mathbb N}$;
--   3. the gaps $T_{n+1}-T_n$ are independent, and each has the law of $T_1-T_0$.
--
--   Iterating Skorokhod's representation puts the entire walk inside one Brownian motion, read at a
--   sequence of stopping times whose increments are i.i.d.
--
--   **Formalization Note** As in Theorem 8.1.1 the probability space is produced rather than
--   assumed, for the same reason: the construction needs an i.i.d. sequence of auxiliary pairs
--   independent of the Brownian motion.
--
--   The book's "$S_n=_d B(T_n)$" is read as equality of the laws of the *whole processes* on
--   sequence space, not as equality of one-dimensional marginals for each $n$; the latter would be
--   strictly weaker and would not support the proof of Donsker's theorem, where the whole embedded
--   path is compared with the Brownian one. Indexing starts at $n=0$ with the empty sum, matching
--   $T_0=0$.
--
--   The gaps are taken as real numbers, differences of the coercions of $T_{n+1}$ and $T_n$; since
--   $T$ is monotone these are non-negative. Independence is joint independence of the whole family,
--   not merely pairwise.
--
--   The hypotheses are satisfiable — any centred law of variance one, for instance the standard
--   Gaussian or the symmetric two-point law — so the statement is not vacuous.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 391 (PDF p. 399), Theorem 8.1.2: 'Let X_1, X_2, ... be i.i.d. with a distribution F, which has mean 0 and variance 1, and let S_n = X_1 + ... + X_n. There is a sequence of stopping times T_0 = 0, T_1, T_2, ... such that S_n =d B(T_n) and T_n - T_{n-1} are independent and identically distributed.' Proof: 'Let (U_1, V_1), (U_2, V_2), ... be i.i.d. and have distribution given in (8.1.1) and let B_t be an independent Brownian motion. Let T_0 = 0, and for n >= 1, let T_n = inf{t >= T_{n-1} : B_t - B(T_{n-1}) not in (U_n, V_n)}.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Definitions.Def_DurrettProbability_Donsker

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem skorokhod_embedding_walk (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 0)
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ) (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ) (_ : IsProbabilityMeasure P)
      (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → MeasurableSpace Ω) (T : ℕ → Ω → ℝ≥0),
      IsBrownianReal B P ∧
      (∀ s t : ℝ≥0, s ≤ t → F s ≤ F t) ∧ (∀ t, F t ≤ mΩ) ∧ (∀ t, pastSigma B t ≤ F t) ∧
      (∀ n, ∀ t : ℝ≥0, MeasurableSet[F t] {ω | T n ω ≤ t}) ∧
      T 0 = 0 ∧ (∀ n ω, T n ω ≤ T (n + 1) ω) ∧
      Measure.map (fun ω (n : ℕ) => B (T n ω) ω) P
        = Measure.map (fun (x : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range n, x k)
            (Measure.infinitePi fun _ : ℕ => μ) ∧
      iIndepFun (fun n ω => (T (n + 1) ω : ℝ) - (T n ω : ℝ)) P ∧
      (∀ n, IdentDistrib (fun ω => (T (n + 1) ω : ℝ) - (T n ω : ℝ))
        (fun ω => (T 1 ω : ℝ) - (T 0 ω : ℝ)) P P) := by sorry

end DurrettProbability
