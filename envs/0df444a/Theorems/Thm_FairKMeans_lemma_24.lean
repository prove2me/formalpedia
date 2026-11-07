-- Prove2me | Theorems.Thm_FairKMeans_lemma_24
-- name    : FairKMeans.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:28.177505+00:00
-- url     : https://prove2.me/theorems/2a61d57d-22a0-46e4-9b52-9b5f9d926c11
-- title:
--   Lemma 24 — the initial pair: $\Psi(\phi^*_{T_0})\le(1+\lambda)L_0$ and $L_0\le(1+\eta)\mathrm{Cost}^\circ$
-- statement:
--   Let $\rho\ge1$, $\varepsilon\in(0,1]$, $\eta=\min\{1/10,\varepsilon/(3\rho)\}$, $\lambda=\rho/(1+\rho)$, and let the instance have a fair solution. Run Algorithm 1 with an exact fair-LP oracle (any LP (29) oracle and any $k$-means oracle). Its initial pair $(T_0,\phi^*_{T_0})$, $T_0=\mathrm{WCS}_\eta(P)$, with $L_0=\mathrm{Cost}(P,T_0,\phi^*_{T_0})$, is a relaxed solution with
--
--   $$C_{T_0}\le L_0,\qquad \Psi(\phi^*_{T_0})\le(1+\lambda)L_0,$$
--
--   and every comparison solution $(S^\circ,\phi^\circ)$ satisfies $L_0\le(1+\eta)\,\mathrm{Cost}(P,S^\circ,\phi^\circ)$.
--
--   This starts the loop inside the region where Lemmas 25–27 apply.
--
--   Differences from the source:
--   - encoding: the initial pair of Algorithm 1, ϕ*_{T0} an optimal solution → the initial fields of alg1 with an oracle that returns an optimal solution whenever one exists; reason: the fair LP of T0 has an optimum under the standing assumption
--   - encoding: standing assumption: the instance has a fair solution (p.19) → hypothesis HasFairSolution; reason: stated once for the whole analysis
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 24, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_CandidateSets
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1
import Definitions.Def_FairKMeans_Comparison

namespace FairKMeans

/-- **Lemma 24 (Initial relaxed solution)**, p.30 (PDF 32). Cheng–Mo–Song–Ding,
arXiv:2609.07974 (held version, sha256 73e9312c…).

The initial pair `(T₀, φ*_{T₀})` of Algorithm 1 (`T₀ = WCS_η(P)`, `φ*_{T₀}` returned by an exact
fair-LP oracle, `L₀ = Cost(P, T₀, φ*_{T₀})`) is a relaxed solution with `C_{T₀} ≤ L₀` and
`Ψ(φ*_{T₀}) ≤ (1+λ)L₀`; furthermore every comparison solution `(S°, φ°)` satisfies
`L₀ ≤ (1+η)Cost(P, S°, φ°)`. The instance has a fair solution (standing assumption, p.19). -/
theorem lemma_24 (ρ ε : ℝ) (hρ : 1 ≤ ρ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {d n m : ℕ}
    (I : Instance d n m) (hfair : HasFairSolution I) (fairLP : FairLPOracle d n)
    (lp29 : LP29Oracle d n) (KM : KMOracle d) (hF : IsFairLPOracle I fairLP) :
    IsRelaxed I (alg1 ρ ε I fairLP lp29 KM).initφ ∧
      CT I (alg1 ρ ε I fairLP lp29 KM).initφ ≤ (alg1 ρ ε I fairLP lp29 KM).L₀ ∧
      Psi I ρ (alg1 ρ ε I fairLP lp29 KM).initφ ≤ (1 + lam ρ) * (alg1 ρ ε I fairLP lp29 KM).L₀ ∧
      ∀ (s₀ : ℕ) (S₀ : Fin s₀ → E d) (φ₀ : Fin n → Fin s₀ → ℝ), IsComparison I S₀ φ₀ →
        (alg1 ρ ε I fairLP lp29 KM).L₀ ≤ (1 + eta ρ ε) * cost I S₀ φ₀ := by sorry

end FairKMeans
