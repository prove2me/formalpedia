-- Prove2me | Theorems.Thm_BQPNotInIP_OracleSep_claim_6_3_1
-- name    : BQPNotInIP.OracleSep.claim_6_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:43.199328+00:00
-- url     : https://prove2.me/theorems/1067619c-431c-4315-afbe-72aa7b511572
-- title:
--   Claim 6.3.1 — conditional scalar rounding error
-- statement:
--   Let $Z\sim\mathcal N(0,1)$, $a,d\in\mathbb R$, $s\in\{-1,1\}$, $1/2\le\tau\le1$, and $0<\delta\le1/2$. Set $G=\sqrt\tau Z+\sqrt{1-\tau}\,d$. Then
--   $$
--   \left|s-\mathbb E\!\left[h_{a,\delta}(G)\mid\operatorname{sgn}(a+G)=s\right]\right|
--   \le3\delta(1+|a|+|d|).
--   $$
--   The conditioning event has positive probability because $a+G$ has variance $\tau\ge1/2$. Its conditional mean is represented by the integral over that event divided by its probability. This is the fixed-value statement proved on the source page, and supplies the scalar estimate used by Lemma 6.3.
--
--   Differences from the source:
--   - generalization: a conditional bound given the random variables S_i,D_i → the bound for every fixed a,d,s,τ in the ranges used in the proof; reason: the pointwise estimate yields the printed conditional bound almost surely
--   - encoding: Gaussian sign rounding → Real.sign, with sign zero equal to zero; reason: every rounded coordinate has positive variance, so zero has probability zero
--   - encoding: conditioning on sign(a+G)=s → a restricted integral divided by the real probability of the event; reason: the event has strictly positive probability under the stated Gaussian variance
-- source:
--   Adam Bouland, Andrew Huang, Anand Natarajan, Itay Shalit, Avishay Tal, BQP ⊆ IP Does Not Relativize, STOC 2027 submission #156 (October 2026), Claim 6.3.1 and its fixed-value proof formulation, PDF p. 17 (printed p. 15). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/156.pdf#page=17

import Definitions.Def_BQPNotInIP_OracleSep_Analysis

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace BQPNotInIP.OracleSep

theorem claim_6_3_1 (a d s τ δ : ℝ)
    (hs : s = 1 ∨ s = -1) (hτ : (1:ℝ)/2 ≤ τ ∧ τ ≤ 1)
    (hδ : 0 < δ ∧ δ ≤ (1:ℝ)/2) :
    let G := fun z : ℝ => Real.sqrt τ*z + Real.sqrt (1-τ)*d
    let E := {z : ℝ | Real.sign (a + G z) = s}
    |s - (∫ z in E, smoothSign a δ (G z) ∂(gaussianReal 0 1)) /
      (gaussianReal 0 1).real E| ≤ 3*δ*(1+|a|+|d|) := by sorry

end BQPNotInIP.OracleSep
