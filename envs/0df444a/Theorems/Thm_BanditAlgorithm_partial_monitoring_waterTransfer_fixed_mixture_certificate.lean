-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_waterTransfer_fixed_mixture_certificate
-- name    : BanditAlgorithm.partial_monitoring_waterTransfer_fixed_mixture_certificate
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T18:02:53.046613+00:00
-- url     : https://prove2.me/theorems/4dab0aa3-a2ff-48c4-8810-befe60f96ec0
-- title:
--   Fixed-mixture water-transfer certificate
-- statement:
--   Let $q$ be a comparator distribution and let $\lambda$ be a mixed outcome. Suppose a family of ancestor sets is reflexive and transitive, the expected loss decreases toward ancestors, and a bounded vector loss estimator is supported only on ancestor–descendant pairs. For every sufficiently small learning rate $\eta$, there are an interior sampling distribution $p$ and a vector estimator $f$ such that every scaled importance-weighted coordinate is at least $-1$, the quadratic stability term is at most $2k^3\max(1,V)^2\eta^2$ for every outcome, and the $\lambda$-averaged exploration loss is at most $k\max(1,V)\eta$.\n\nThe construction applies Lemma 37.20 to transfer comparator mass toward the observing ancestors and then mixes the result with uniform exploration.\n\n**Formalization Note** This isolates the complete analytic calculation on pp. 501–502; Lemma 37.21 supplies the ancestor sets and path-summed local estimators in the geometric child theorem.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press (2020), §37.7, Theorem 37.17 and Lemma 37.20, printed pp. 500–502, especially Eq. (37.17) and the stability calculation. https://tor-lattimore.com/downloads/book/book.pdf

import Theorems.Thm_BanditAlgorithm_waterTransfer_distribution_of_ancestor_sets
import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

theorem BanditAlgorithm.partial_monitoring_waterTransfer_fixed_mixture_certificate
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
      (∀ a σ b, -1 ≤ η * f a σ b / p a) ∧
      (∀ i : Fin d,
        ∑ a : Fin k, p a *
          (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
            η ^ 2 * (2 * (k : ℝ) ^ 3 * (max 1 V) ^ 2)) ∧
      ∑ i : Fin d, lam i * (∑ a : Fin k, (p a - q a) * G.L a i) ≤
        η * ((k : ℝ) * max 1 V) := by sorry
