-- Prove2me | Theorems.Thm_CHMSPricing_SpmMatroid_spm_two_approx_matroid
-- name    : CHMSPricing.SpmMatroid.spm_two_approx_matroid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:41:29.635103+00:00
-- url     : https://prove2.me/theorems/ab9c9d4b-b977-4a82-b258-3ee05c55597f
-- title:
--   Theorem 5, p. 6 — under a matroid constraint the sequential posted-price mechanism S 2-approximates the optimal revenue
-- statement:
--   Consider the Bayesian single-parameter mechanism design problem with $n$ agents whose values $v_i \sim F_i$ are independent and regular, and a matroid feasibility constraint $\mathcal J$. Let $M$ be any truthful mechanism, with service probabilities $q^M_i$. Let $\mathcal S$ be the sequential posted-price mechanism that posts to agent $i$ the price $p_i = F_i^{-1}(1 - q^M_i)$, so that agent $i$ accepts with probability exactly $q^M_i$, and approaches the agents in decreasing order of price. Then
--
--   $$\mathcal R^M \le 2\, \mathcal R^\sigma_{\mathbf p}.$$
--
--   A take-it-or-leave-it mechanism, with no competition between the agents, thus loses at most half of the optimal revenue under a matroid constraint.
--
--   **Formalization Note** The paper builds $\mathcal S$ from Myerson's optimal mechanism and compares with its revenue. The statement here is for every truthful $M$, with $\mathcal S$ built from $M$'s own service probabilities; taking $M$ to be Myerson's mechanism gives the paper's statement, and the form is stronger. It follows from the same proof, because Lemma 2 and the rank bound hold for every truthful $M$. Prices are given as arguments with $p_i \in [\underline v_i, \overline v_i]$ and $F_i(p_i) = 1 - q^M_i$; ties in the price order are arbitrary. Distributions have a positive density on a bounded interval (no point masses), so the randomized variant of $\mathcal S$ does not arise.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 6, Theorem 5

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Mechanism
import Definitions.Def_CHMSPricing_SpmMatroid_Spm

namespace CHMSPricing.SpmMatroid

/-- Theorem 5 (p. 6): under a matroid feasibility constraint and regular value distributions,
for every truthful mechanism `M`, the SPM `𝒮` with prices `pᵢ = Fᵢ⁻¹(1 − q^M_i)` that
approaches the agents in decreasing order of price earns at least half of `M`'s revenue. -/
theorem spm_two_approx_matroid {n : ℕ} (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (M : Mechanism (Fin n)) (hM : IsTruthful D J M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ 2 * spmRevenue D J σ p := by sorry

end CHMSPricing.SpmMatroid
