-- Prove2me | Theorems.Thm_CaiZhuInfo_Matrix_compound_poisson_bound
-- name    : CaiZhuInfo.Matrix.compound_poisson_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:16.389831+00:00
-- url     : https://prove2.me/theorems/558dba91-3523-468c-ba62-ec3126e4ebeb
-- title:
--   Corollary 4.4 — Compound-Poisson convolution bound
-- statement:
--   Let $Q$ have finite positive support of size $s\ge2$ on any discrete group, and let $n=\lfloor\log_2s\rfloor$. For any $\lambda\ge0$, independently choose $K_\lambda\sim\mathrm{Pois}(\lambda)$ and take the ordered product of $K_\lambda$ independent $Q$ factors, with law $P_\lambda$. Then
--   $$\|P_\lambda\|_\infty\le\mathbb E\|Q^{*K_\lambda}\|_\infty\le C_0\exp((n\ln2-\lambda)^+)2^{-H(Q)}.$$
--   Both inequalities hold, including at rate zero and for infinite noncommutative groups. The count law is the full Poisson law, and the compound distribution need not have finite support. This is the entropy-conversion result needed for prediction.
--
--   Differences from the source:
--   - encoding: the compound-Poisson law and expectation over its independent count → the full nonnegative point-mass series and Poisson-weighted series of convolution norms; reason: conditioning on every possible count gives exactly these convergent series; no truncation or ambient-group restriction is made
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), Corollary 4.4, (20), printed p.14 / PDF p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_compoundPoissonPoint

open MeasureTheory
open scoped Classical ENNReal

namespace CaiZhuInfo.Matrix

theorem compound_poisson_bound {G : Type} [Group G] (Q : PMF G)
    (hQ : Q.support.Finite) (hs : 2 ≤ hQ.toFinset.card) (rate : ℝ) (hrate : 0 ≤ rate) :
    largestPoint (compoundPoissonPoint Q rate) ≤
      (∑' k : ℕ, poissonWeight rate k * largestPoint (mass (convolutionPower Q k))) ∧
    (∑' k : ℕ, poissonWeight rate k * largestPoint (mass (convolutionPower Q k))) ≤
      C₀ * Real.exp (max ((Nat.log2 hQ.toFinset.card : ℝ) * Real.log 2 - rate) 0) *
        (2 : ℝ) ^ (-supportedEntropy Q hQ) := by sorry

end CaiZhuInfo.Matrix
