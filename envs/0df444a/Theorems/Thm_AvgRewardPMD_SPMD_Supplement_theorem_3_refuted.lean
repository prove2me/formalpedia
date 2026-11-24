-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_Supplement_theorem_3_refuted
-- name    : AvgRewardPMD.SPMD.Supplement.theorem_3_refuted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:26:54.749844+00:00
-- url     : https://prove2.me/theorems/738f42d4-134f-43aa-9efb-c392577da308
-- title:
--   Theorem 3, p. 14 (corrected: the printed bound is false at K = 2 with an exact critic; stated as its refutation) — the bound on E[D(π_{K+1},π*)] under the stepsize (3.18) does not hold
-- statement:
--   Theorem 3 of the paper asserts the following. Let $\mathcal M$ be a finite AMDP satisfying Assumptions 1 and 2, $\Gamma\in(0,1)$ with $\min_s\nu^\pi(s)\ge1-\Gamma$ for every feasible $\pi$, $h^\pi$ convex with modulus $\omega>0$ in the sense of (2.2), $\pi^*$ an optimal policy with stationary distribution $\nu^*$, and $D(\pi,\pi')=\mathbb E_{s\sim\nu^*}[D^{\pi'}_\pi(s)]$. Run SPMD from $\pi_0(a\mid s)=1/|\mathcal A|$ under Assumption 3 (constants $\varsigma,\sigma,\kappa$) with the constant stepsize
--   $$\lambda=\min\Big\{\frac{1-\Gamma}{\omega\Gamma},\frac{q\log K}{\omega K}\Big\},\qquad q=2\Big(1+\log\frac{8\Gamma(1-\Gamma)\omega^2D(\pi_0,\pi^*)+8\Gamma(1-\Gamma)\omega(\rho(\pi_0)-\rho(\pi^*))}{\sigma^2}\Big).\tag{3.18}$$
--   Then
--   $$\mathbb E[D(\pi_{K+1},\pi^*)]\le\frac{\Gamma^K}{\omega}\big(\rho(\pi_0)-\rho(\pi^*)\big)+\Gamma^KD(\pi_0,\pi^*)+\frac{\sigma^2}{4\omega^2\Gamma(1-\Gamma)K}(1+q\log K)+\frac{2\varsigma}{\omega\Gamma}.$$
--
--   **This item states that the assertion is false**, even on the part of its domain where every expression is defined and the stepsize is positive: $K\ge2$, $\sigma>0$, a positive argument of the logarithm, and $q>0$.
--
--   A counterexample: one state, two actions, $\omega=1$, $h(p)=\sum_ap(a)\log p(a)$ and a cost $c$ with $\pi^*=(0.6,0.4)$ the optimal policy (the softmax of $-c$), $\Gamma=10^{-5}$ (admissible, since $\nu^\pi=1$), an exact critic $\bar{\mathcal Q}^{\pi_k,\zeta_k}=\bar Q^{\pi_k}$ (so $\varsigma=0$ and (3.8) holds for every $\sigma\ge0$), $K=2$, and $\sigma^2=X/10^{13}$ with $X$ the numerator in (3.18). Then $q\approx61.87$, $\lambda\approx21.44$, the iterates are $\log\pi_{k+1}=(\log\pi_k+\lambda\omega\log\pi^*)/(1+\lambda\omega)$ up to normalization, and $D(\pi_3,\pi^*)\approx1.54\times10^{-10}$ exceeds the right side $\approx4.23\times10^{-12}$. The proof fails at (3.20), whose step $(1+q\log K/K)^{-K}\le\exp(-\tfrac12q\log K)$ fails at the example’s $q\log K/K\approx21.44$; at $K=1$ the stepsize is $0$, and the bound fails as well.
--
--   The strongly convex SPMD analysis of the paper (Lemma 6) remains valid; only the explicit last-iterate tuning of Theorem 3 is wrong as printed.
--
--   **Formalization Note** The negated claim quantifies over finite types in `Type` (a counterexample there refutes the universe-polymorphic claim), with a lower semicontinuous regularizer on the simplex, nonnegative bias and κ, and an integrable final distance, as well as the hypotheses of the published conventions: Assumption 3 is `CriticAssumption` plus (3.8) for the critic outputs $k\le K$, $\rho$ is evaluated at a start state $s_0$, and the optimality of $\pi^*$ is stated against every feasible policy.
--
--   Differences from the source:
--   - correction: the bound of Theorem 3 holds for every K under (3.18) → the negation: some instance satisfying every hypothesis violates the bound; reason: counterexample: one state, two actions, ω = 1, entropy regularizer, π* = (0.6, 0.4), Γ = 1e-5, exact critic (ς = 0), K = 2, σ² = X/1e13 gives q ≈ 61.87, λ ≈ 21.44, E[D(π_3, π*)] ≈ 1.54e-10 > 4.23e-12, the right side; see DISPROOF.md
--   - generalization: the printed hypotheses → the printed hypotheses plus K ≥ 2, σ > 0, a positive logarithm argument, q > 0, and an integrable final distance; reason: the deterministic counterexample satisfies all these restrictions; refutation in this smaller domain rules out zero stepsizes, undefined logarithms and totalized integrals as the cause
--   - encoding: types of any universe → S, A, Ω in Type; reason: a counterexample in Type refutes the universe-polymorphic claim
--   - reading: (2.2) for π′ ranging over all policies → (2.2) at strictly positive π′ only (the published IsKLStrongConvex); reason: at a boundary π′ with ω > 0 no finite h satisfies (2.2); every SPMD iterate is strictly positive; this is the convention of the published base mission
--   - encoding: ρ(π), a scalar → ρ^π(s₀) = avgCost at an arbitrary start state s₀; reason: under Assumption 1 the average cost does not depend on the start state (§2.1, p. 6), as in the published base items
--   - encoding: h is closed convex; ς, κ ≥ 0 → hconv together with lower semicontinuity on each simplex; explicit bias ≥ 0 and κ ≥ 0; reason: on the compact simplex lower semicontinuity expresses closedness of the finite-valued regularizer; these are original source restrictions, also met by the entropy counterexample
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 14, Theorem 3 and (3.18); proof pp. 14–15, (3.19)–(3.21)

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting
import Definitions.Def_AvgRewardPMD_SPMD_Supplement_Actor

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning MeasureTheory

theorem theorem_3_refuted :
    ¬ ∀ (S A : Type) [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
      (P : S → A → S → ℝ) (_hP : IsTransitionKernel P) (_hmix : IsMixing P)
      (_herg : IsErgodic P)
      (c : S → A → ℝ) (h : S → (A → ℝ) → ℝ) (ω : ℝ) (_hω : 0 < ω)
      (_hconv : IsKLStrongConvex h ω)
      (_hclosed : ∀ s, LowerSemicontinuousOn (h s) (stdSimplex ℝ A)) (Γ : ℝ) (_hΓ : IsGammaBound P Γ)
      (πstar : S → A → ℝ) (_hπstar : IsPolicy πstar) (s₀ : S)
      (_hopt : ∀ π' : S → A → ℝ, IsPolicy π' →
        avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀
          ≤ avgCost P π' (fun s a => c s a + h s (π' s)) s₀)
      (νstar : S → ℝ) (_hνstar : MarkovMixing.IsStationary (stateMatrix P πstar) νstar)
      (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
      (bias σ κ : ℝ) (_hbias : 0 ≤ bias) (_hκ : 0 ≤ κ) (K : ℕ) (_hK : 2 ≤ K) (_hσ : 0 < σ)
      (_hcrit : CriticAssumption μ ℱ (fun π' => diffQ P π' (fun s a => c s a + h s (π' s)))
        Qhat π bias κ (K + 1))
      (_hvar : CriticVariance μ ℱ (fun π' => diffQ P π' (fun s a => c s a + h s (π' s)))
        Qhat π σ (K + 1))
      (_hlogarg : 0 < 8 * Γ * (1 - Γ) * ω ^ 2 * stationaryKL νstar uniformPolicy πstar
        + 8 * Γ * (1 - Γ) * ω
          * (avgCost P uniformPolicy (fun s a => c s a + h s (uniformPolicy s)) s₀
            - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀))
      (q : ℝ)
      (_hq : q = 2 * (1 + Real.log ((8 * Γ * (1 - Γ) * ω ^ 2
          * stationaryKL νstar uniformPolicy πstar
        + 8 * Γ * (1 - Γ) * ω
          * (avgCost P uniformPolicy (fun s a => c s a + h s (uniformPolicy s)) s₀
            - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀)) / σ ^ 2)))
      (_hqpos : 0 < q)
      (lam : ℝ)
      (_hlam : lam = min ((1 - Γ) / (ω * Γ)) (q * Real.log K / (ω * K)))
      (_hiter : IsSPMDIterates h (fun _ => lam) Qhat π)
      (_hintD : Integrable (fun ξ => stationaryKL νstar (π (K + 1) ξ) πstar) μ),
      ∫ ξ, stationaryKL νstar (π (K + 1) ξ) πstar ∂μ
        ≤ Γ ^ K / ω
            * (avgCost P uniformPolicy (fun s a => c s a + h s (uniformPolicy s)) s₀
              - avgCost P πstar (fun s a => c s a + h s (πstar s)) s₀)
          + Γ ^ K * stationaryKL νstar uniformPolicy πstar
          + σ ^ 2 / (4 * ω ^ 2 * Γ * (1 - Γ) * K) * (1 + q * Real.log K)
          + 2 * bias / (ω * Γ) := by sorry

end AvgRewardPMD.SPMD.Supplement
