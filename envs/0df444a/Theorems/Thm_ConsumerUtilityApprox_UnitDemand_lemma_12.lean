-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_lemma_12
-- name    : ConsumerUtilityApprox.UnitDemand.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:55:37.25093+00:00
-- url     : https://prove2.me/theorems/1b4e519f-c181-463d-b4e6-f78e8d5cc8cb
-- title:
--   Lemma 12 — average utility minus excess requests ≥ OPT^{n,m}/(2 + e/(e − 1)) − nm/√T − n(δ + γ)
-- statement:
--   Work in normalized units: an instance with $n,m\ge1$ and $\sum_{i,j}\mathbb E[V_{ij}]=1$. Fix $\delta,\gamma\in(0,1]$ and $T\ge1$ rounds, step size $\eta=1/(n\sqrt T)$, initial demand weights $\lambda^1=0$. In round $t$, buyer $i$'s mechanism $M^t_i$ is $M^{1,m}_{\mathrm{het}}$ for $\lambda^t$: with probability $e/(3e-2)$ independent posted prices drawn from two-point laws implementing $\mathrm{OPT}^{1,1}(V_{ij};q^{t,i}_j)$, where the caps $q^{t,i}$ are feasible for the cap program (5.4) and within $\delta$ of its optimum $R_{\lambda^t}$; otherwise free lotteries $\ell_j(b)$ with $b>0$ and $2b-2\gamma\le U(M^{\mathrm{free}}_b)\le2b$. With $r^t_j=\sum_iq^{\mathrm{alloc}}_j(M^t_i)$ and $\lambda^{t+1}_j=\min\{1,\max\{0,\lambda^t_j+\eta(r^t_j-1)\}\}$, let $\bar U=\frac1T\sum_t\sum_iU(M^t_i)$ and $\bar r_j=\frac1T\sum_tr^t_j$. Then
--   $$\bar U-\sum_j(\bar r_j-1)^+\ \ge\ \frac{\mathrm{OPT}^{n,m}}{2+e/(e-1)}-\frac{nm}{\sqrt T}-n(\delta+\gamma).$$
--   With (C.5) this gives Lemma 6.
--
--   Differences from the source:
--   - encoding: values in R_+, laws F_j, items 1..m → ℝ≥0, ProbabilityMeasure ℝ≥0, Fin m; product law vecLaw; reason: Lean conventions for the same objects
--   - encoding: rounds t = 1, …, T with λ^1 = 0 → rounds t = 0, …, T − 1 with lam 0 = 0; reason: index shift
--   - reading: δ and γ are the additive errors in cap optimization and free-lottery computation for each buyer at each round → hypotheses: the caps are feasible for (5.4) with objective ≥ R_λ − δ (Lemma 11's guarantee), the prices implement OPT^{1,1} at those caps, and the lottery parameter b > 0 has 2b − 2γ ≤ U(M^free_b) ≤ 2b (Appendix C.3's guarantee); reason: these are exactly the guarantees the proof of Lemma 12 uses (p. 46), and the greedy caps and the bisection output satisfy them
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 45, Lemma 12 (proof pp. 46–48)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem lemma_12 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (I : Instance n m)
    (hnorm : ∑ i, ∑ j, mean (I.F i j) = 1)
    (δ γ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (T : ℕ) (hT : 1 ≤ T)
    (lam : ℕ → Fin m → ℝ) (caps : ℕ → Fin n → Fin m → ℝ)
    (pr : ℕ → Fin n → Fin m → TwoPointPrice) (b : ℕ → Fin n → ℝ)
    (hcaps : ∀ t < T, ∀ i, IsFeasibleCaps (caps t i) ∧
      capOpt (I.F i) (lam t) - δ ≤ capObjective (I.F i) (lam t) (caps t i))
    (hpr : ∀ t < T, ∀ i j, IsImplementing (I.F i j) (caps t i j) (pr t i j))
    (hb : ∀ t < T, ∀ i, 0 < b t i ∧
      2 * b t i - 2 * γ
        ≤ utility (I.buyerLaw i) (freeLotteryMech (lotteryProb (lam t) (b t i))).reduced ∧
      utility (I.buyerLaw i) (freeLotteryMech (lotteryProb (lam t) (b t i))).reduced
        ≤ 2 * b t i)
    (hlam0 : ∀ j, lam 0 j = 0)
    (hlam : ∀ t < T, ∀ j, lam (t + 1) j =
      min 1 (max 0 (lam t j + 1 / ((n : ℝ) * Real.sqrt T) *
        (∑ i, qAlloc (I.buyerLaw i)
          (hetMech (pr t i) (lotteryProb (lam t) (b t i))).reduced j - 1)))) :
    OPT I / (2 + Real.exp 1 / (Real.exp 1 - 1)) - (n : ℝ) * m / Real.sqrt T - n * (δ + γ)
      ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ i,
          utility (I.buyerLaw i) (hetMech (pr t i) (lotteryProb (lam t) (b t i))).reduced
        - ∑ j, max ((1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ i,
            qAlloc (I.buyerLaw i) (hetMech (pr t i) (lotteryProb (lam t) (b t i))).reduced j
              - 1) 0 := by sorry

end ConsumerUtilityApprox.UnitDemand
