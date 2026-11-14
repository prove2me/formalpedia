-- Prove2me | Theorems.Thm_BilateralProfitRegular_eq_55
-- name    : BilateralProfitRegular.eq_55
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:34.677409+00:00
-- url     : https://prove2.me/theorems/252ff286-803f-4352-b67e-04d8e767fd42
-- title:
--   Eq. (55) — ConOpt on a candidate: $\mathbb E[\sum_\tau(L(x_\tau)-\min_{\mathcal K_i}L)]\le(C/\delta)\sqrt n\log^2(2n)$
-- statement:
--   Let $C_1>0$ be the constant of the observation bound (50). There is a constant $C$ with the following property. For every $\delta>0$, every nonempty compact convex $\mathcal K\subseteq\mathrm{int}(\mathcal T)$ and every $n\ge1$, there is an $n$-query algorithm on $\mathcal K$ (ConOpt applied to the scaled problem) such that
--   $$\mathbb E\Big[\sum_{\tau=1}^n\big(L(x_\tau)-\min_{\mathcal K}L\big)\Big]\le\frac C\delta\sqrt n\log^2(2n),\qquad L=1/r_\lambda,$$
--   holds under the following conditions:
--
--   - the distributions are regular;
--   - $\lambda>0$ satisfies $0.99\delta\le r_\lambda\le6\delta$ on $\mathcal K$, which is eq. (52);
--   - the observations have conditional mean $L(x)$ and values in $[0,C_1/\delta]$, which is eq. (50).
--
--   Differences from the source:
--   - generalization: a valid candidate's region $\mathcal K_i$ and a calibrated $\lambda$ (context of p.43) → any nonempty compact convex $\mathcal K\subseteq\mathrm{int}(\mathcal T)$ and any $\lambda>0$ with (52) on $\mathcal K$; reason: the derivation uses only these properties; candidates and calibrated parameters satisfy them
--   - encoding: constants of (50) and (55); "$\tau$ indexing the virtual convex optimization time" → $\forall C_1\,\exists C$; observation kernels with mean $L(x)$ and values in $[0,C_1/\delta]$; the algorithm chosen before $E$, $\lambda$ and the kernels; reason: $C$ is fixed after $C_1$, as in the paper
--   - encoding: independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities (§2, §6) → `RegularUnit E` for a published `Environment` `E` (supports $[0,1]$, `E.Regular`); $P$, $\mu$ from the joint law `E.prior`, $F_s,F_b$ = `E.cdfS`, `E.cdfB`; reason: the same class: Definitions 2.1–2.2 with the standing positivity of the densities; the valuation laws are the environment's
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), eq. (55), p.43 (PDF 45)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary
import Definitions.Def_BilateralProfitRegular_ConvexBandit

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade

/-- **Eq. (55)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.43
(PDF 45): ConOpt (Corollary 3.1's algorithm, run on the scaled loss `δL` with the scaled
observations `δY_x`) on a candidate region `𝒦_i` with `L = 1/r_λ` satisfies, for the non-scaled
loss, `E[∑_{τ=1}^n (L(x_τ) − min_{𝒦_i} L)] ≤ (C/δ) √n log²(2n)`.

**Formalization Note.** The context of p.43 enters as hypotheses: `𝒦` nonempty, compact, convex,
inside `int(𝒯)` (Lemma 6.4); `0.99δ ≤ r_λ ≤ 6δ` on `𝒦` (eq. (52)); observations with conditional
mean `L(x)` and values in `[0, C₁/δ]` (eq. (50)). `C₁` is the constant of (50), fixed before `C`.
The `n`-query algorithm depends only on `𝒦`, `n`, `δ` (and `C₁`), and is chosen before the
environment, `λ` and the observation law. Every `n ≥ 1`. -/
theorem eq_55 :
    ∀ C₁ : ℝ, 0 < C₁ → ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → ∀ K : Set (ℝ × ℝ), K.Nonempty → IsCompact K → Convex ℝ K → K ⊆ intT →
      ∀ n : ℕ, 1 ≤ n →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (alg : BanditAlg (ℝ × ℝ) Ω),
        alg.QueriesIn K ∧
        ∀ E : Environment, RegularUnit E → ∀ lam : ℝ, 0 < lam →
          (∀ x ∈ K, 99 / 100 * δ ≤ auxProfit E lam x ∧ auxProfit E lam x ≤ 6 * δ) →
          ∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) K →
            ν.ValuesIn K (Set.Icc 0 (C₁ / δ)) →
            alg.regret ν Pω n (fun x => 1 / auxProfit E lam x) K ≤
              ENNReal.ofReal (C / δ * Real.sqrt n * Real.log (2 * n) ^ 2) := by sorry

end BilateralProfitRegular
