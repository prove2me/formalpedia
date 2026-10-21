-- Prove2me | Theorems.Thm_DistribRQ_UpperBound_app_A_8
-- name    : DistribRQ.UpperBound.app_A_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:31.569981+00:00
-- url     : https://prove2.me/theorems/aaafbf43-1fd2-40fb-9547-69ef522bae77
-- title:
--   App. A (8), p. A4 — Γ̂(IL0(t)) ≤ Γ̄(IL0(t)) = Ĝ(IL0(t)) + Σᵢ Cᵢ(rᵢ,Qᵢ)
-- statement:
--   Consider the one-warehouse, $N$-retailer system ($N\ge1$) under a modified echelon $(r,Q)$ policy. Let $\kappa$ be a Markov kernel that assigns to every warehouse echelon inventory level $x$ a probability law $\kappa(x)$ of the vector of retailer inventory positions, concentrated on the feasible states at $x$. Let $c=(c_i)$ be an admissible family of measurable, nonnegative retailer charges, and let
--   $$
--   \hat\Gamma(x)=\int\sum_{i=1}^Nc_i(z_i)\,\kappa(x)(dz)
--   $$
--   be the expected retailer cost rate at level $x$. Then for every $x$,
--   $$
--   \hat\Gamma(x)\le\bar\Gamma(x)=\hat G(x)+\sum_{i=1}^NC_i(r_i,Q_i),
--   $$
--   where $\bar\Gamma$ is the envelope of Lemma 3 and $\hat G=\bar\Gamma-\sum_iC_i$ is (5).
--
--   This is the first step of the proof of Theorem 1: it rewrites the Lemma 3 bound through $\hat G$, the function the warehouse-level cost $\Lambda_0$ is built from.
--
--   **Formalization Note** The conditional law of the retailer positions given $IL_0(t)$ is not computed in the paper; the statement holds for every Markov kernel supported on the feasible states, which covers it. Measurability and nonnegativity of the charges (cost rates) are added so that $\hat\Gamma$ is a genuine integral.
-- source:
--   Zhu, Chen, Hu & Yang, A simple heuristic policy for stochastic distribution inventory systems with fixed shipment costs, SSRN 2921743 (2020-09-08 copy), p. A4 (PDF 23), Online Appendix A, proof of Theorem 1, App. A (8)

import Mathlib
import Definitions.Def_DistribRQ_UpperBound_Model

open MeasureTheory ProbabilityTheory

namespace DistribRQ.UpperBound

/-- App. A (8), p. A4 (Zhu, Chen, Hu & Yang, SSRN 2921743): `Γ̂(x) ≤ Γ̄(x) = Ĝ(x) + Σᵢ Cᵢ(rᵢ,Qᵢ)`,
where `Γ̂(x)` is the expected retailer charge when the retailer inventory positions have law
`κ x`, supported on the feasible states at echelon level `x`. -/
theorem app_A_8 {N : ℕ} [NeZero N] (P : Primitives N) (π : Policy N) (κ : Kernel ℝ (Fin N → ℝ)) [IsMarkovKernel κ] (hκ : ∀ x, κ x (Feasible π x)ᶜ = 0) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c) (hc_meas : ∀ i, Measurable (c i)) (hc_nonneg : ∀ i z, 0 ≤ c i z) (x : ℝ) : GammaHat κ c x ≤ GammaBar P π x ∧ GammaBar P π x = Ghat P π x + ∑ i, Ccost P π i := by sorry

end DistribRQ.UpperBound
