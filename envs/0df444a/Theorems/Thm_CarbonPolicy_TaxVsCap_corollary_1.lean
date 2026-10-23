-- Prove2me | Theorems.Thm_CarbonPolicy_TaxVsCap_corollary_1
-- name    : CarbonPolicy.TaxVsCap.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:13.579984+00:00
-- url     : https://prove2.me/theorems/bd152a2a-59a8-4fee-8776-3c7581fa4729
-- title:
--   Corollary 1: consumer-surplus window and emissions under the two policies
-- statement:
--   Fix $b,\beta,\gamma^+,w$ and moments $\bar a,\bar k,\sigma_D,\sigma$ satisfying the standing conditions. The thresholds $R$ and $R_0$ are the paper's explicit functions of these parameters. Then:
--
--   1. There are two numbers $R_1<R<R_0<R_2$, chosen uniformly for all admissible joint distributions with these moments, such that for every pair of optimal intensities,
--   $$CS_T>CS_C\quad\Longleftrightarrow\quad R_1<\rho<R_2.$$
--   2. If $\rho<R_0$, then $S_T<S_C$ when $\gamma_T^*+\gamma_C^*<\bar a/\bar k$; otherwise $S_T\ge S_C$. If $\rho>R_0$, then $S_T>S_C$ under the same strict inequality; otherwise $S_T\le S_C$.
--
--   The theorem gives the paper's consumer-surplus and emissions comparisons in the base model.
--
--   **Formalization Note** Both intensities are arbitrary maximizers of their expectation-based objectives on $[0,\gamma^+]$. The uniform quantifier places $R_1,R_2$ before the probability model. The parameter hypotheses include $\bar a\bar k<4b\beta\gamma^+$ and $\gamma^+\bar k<\bar a$, which are the correlation-free consequences of Assumption 1 and its almost-sure demand clause.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), pp. 19–20, Corollary 1(a)–(b)

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

theorem corollary_1 (b β γp w A K D S : ℝ)
    (hb : 0 < b) (hγp : 0 < γp) (hK : 0 < K)
    (hD : 0 < D) (hS : 0 < S)
    (hcurvature : K ^ 2 + S ^ 2 < 4 * b * β)
    (hinvestment : A * K < 4 * b * β * γp)
    (hdemand : γp * K < A) :
    (∃ R1 R2 : ℝ,
      R1 < R b β γp A K D S ∧ R b β γp A K D S < R0 b β γp A K D S ∧ R0 b β γp A K D S < R2 ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (M : Model Ω)
        (hbarA : abar M.P M.a = A) (hbarK : kbar M.P M.k = K)
      (hsD : sigmaD M.P M.a = D) (hs : sigma M.P M.k = S)
      (hA : Assumption1 M b β γp) (γT γC : ℝ)
      (hT : OptimalTax M b β γp w γT)
      (hC : OptimalCap M b β γp w γC),
        (CSC M b γC < CST M b γT ↔
          R1 < rho M.P M.a M.k ∧ rho M.P M.a M.k < R2)) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (M : Model Ω)
      (hbarA : abar M.P M.a = A) (hbarK : kbar M.P M.k = K)
      (hsD : sigmaD M.P M.a = D) (hs : sigma M.P M.k = S)
      (hA : Assumption1 M b β γp) (γT γC : ℝ)
      (hT : OptimalTax M b β γp w γT)
      (hC : OptimalCap M b β γp w γC),
      (rho M.P M.a M.k < R0 b β γp A K D S →
        ((γT + γC < A / K → ST M b γT < SC M b γC) ∧
         (¬ (γT + γC < A / K) → SC M b γC ≤ ST M b γT))) ∧
      (R0 b β γp A K D S < rho M.P M.a M.k →
        ((γT + γC < A / K → SC M b γC < ST M b γT) ∧
         (¬ (γT + γC < A / K) → ST M b γT ≤ SC M b γC)))) := by sorry

end CarbonPolicy.TaxVsCap
