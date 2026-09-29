-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_waterTransfer_fixed_mixture_compact_certificate
-- name    : BanditAlgorithm.partial_monitoring_waterTransfer_fixed_mixture_compact_certificate
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T19:49:47.486367+00:00
-- url     : https://prove2.me/theorems/20ccdac8-38b2-44ec-b0eb-47f19d812ca5
-- title:
--   Water-transfer certificate with compactness bounds
-- statement:
--   Let a finite partial-monitoring game have losses in $[0,1]$, let $q$ be a comparator distribution supported on $S$, and fix an outcome mixture $\lambda$. Suppose $f_0$ is a vector loss estimator bounded by $V$, supported along a transitive ancestor relation, and every ancestor has no larger $\lambda$-expected loss than its descendant. For a learning rate $\eta>0$ satisfying $\eta k\max\{1,V\}\le 1/2$, there exist an interior action distribution $p$ and a vector estimator $f$ such that
--
--   $$
--   p_a\ge \eta\max\{1,V\},\qquad |f(a,\sigma,b)|\le V,
--   $$
--
--   the importance-weighted estimates satisfy $-1\le \eta f(a,\sigma,b)/p_a$, their outcome-wise quadratic cost is at most $2\eta^2 k^3\max\{1,V\}^2$, and the $\lambda$-weighted exploration loss is at most $\eta k\max\{1,V\}$.
--
--   This is the bounded form of the fixed-mixture water-transfer certificate; the explicit lower and upper coordinate bounds make the family of certificates compact for the subsequent minimax argument.
--
--   **Formalization Note** The statement retains bounds already supplied by the uniform-exploration mixture in the water-transfer construction.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Chapter 37, Theorem 37.17 and Lemmas 37.20–37.21, printed pp. 500–502, especially Eq. (37.16). https://tor-lattimore.com/downloads/book/book.pdf

import Theorems.Thm_BanditAlgorithm_waterTransfer_distribution_of_ancestor_sets
import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

theorem BanditAlgorithm.partial_monitoring_waterTransfer_fixed_mixture_compact_certificate
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin k)) (q : Fin k → ℝ) (hq : PMSupportedOn S q)
    (lam : Fin d → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin d))
    (anc : Fin k → Finset (Fin k))
    (hself : ∀ b, b ∈ anc b)
    (htrans : ∀ a b, a ∈ anc b → ∀ c, b ∈ anc c → a ∈ anc c)
    (f₀ : Fin k → 𝕊 → Fin k → ℝ)
    (hfvec : PMVectorEstimatorOn G S f₀)
    (V : ℝ) (hV : 0 ≤ V)
    (hfbound : ∀ a σ b, |f₀ a σ b| ≤ V)
    (hfsupp : ∀ a σ b, f₀ a σ b ≠ 0 → a ∈ anc b)
    (hloss : ∀ a b, a ∈ anc b →
      ∑ i : Fin d, G.L a i * lam i ≤ ∑ i : Fin d, G.L b i * lam i)
    (η : ℝ) (hη : 0 < η)
    (hηsmall : η * ((k : ℝ) * max 1 V) ≤ 1 / 2) :
    ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
      PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
      (∀ a, η * max 1 V ≤ p a) ∧
      (∀ a σ b, |f a σ b| ≤ V) ∧
      (∀ a σ b, -1 ≤ η * f a σ b / p a) ∧
      (∀ i : Fin d,
        ∑ a : Fin k, p a *
          (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
            η ^ 2 * (2 * (k : ℝ) ^ 3 * (max 1 V) ^ 2)) ∧
      ∑ i : Fin d, lam i * (∑ a : Fin k, (p a - q a) * G.L a i) ≤
        η * ((k : ℝ) * max 1 V) := by sorry
