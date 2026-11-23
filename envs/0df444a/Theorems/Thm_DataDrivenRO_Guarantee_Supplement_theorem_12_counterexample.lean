-- Prove2me | Theorems.Thm_DataDrivenRO_Guarantee_Supplement_theorem_12_counterexample
-- name    : DataDrivenRO.Guarantee.Supplement.theorem_12_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:50:21.128418+00:00
-- url     : https://prove2.me/theorems/1c94bb3e-f203-4f85-874f-5c4535181130
-- title:
--   Theorem 12 (corrected: counterexample to the printed inverse-norm SDP)
-- statement:
--   Use $d=1$, box $[-2,2]$, sample $(-2,2)$, mean $\hat\mu=0$, population covariance $\hat\Sigma=4$, $C=1/2$, $g_1=1/16$, $g_2=1$, and $\epsilon=999/1000$. The covariance is positive definite, $C^TC=\hat\Sigma^{-1}$, and both the empirical law and $P=\delta_{1/2}$ lie in $\mathcal P^{DY}$. For the nonempty compact convex set $U$ of (36),
--   $$
--   1/2\in U,\qquad \delta^*(1\mid U)\ge1/2=\operatorname{VaR}^P_\epsilon(1),\qquad 190/999<1/2.
--   $$
--   Yet $190/999$ is a feasible value of the printed SDP. Therefore neither the support nor the supremum of admissible VaRs is the greatest lower bound of its feasible values.
--
--   This counterexample refutes the full equality chain of Theorem 12 under the declared norm convention; it makes no separate claim that the probabilistic guarantee or the support/worst-VaR equality fails. The data, empirical membership, LMIs and rational witnesses are documented in DISPROOF.md. The suspected repair is the covariance-weighted dual norm, not an additional assumption excluding this nondegenerate sample.
--
--   Differences from the source:
--   - correction: Theorem 12 equates support and worst-case VaR with the printed SDP infimum → a nondegenerate rational counterexample to the conjunction, including explicit non-IsGLB conclusions for both candidate values; reason: PDF 27 has the inverse-norm subscript; the feasible value 190/999 is smaller than the admissible point and VaR 1/2; the scalar SDP witnesses are retained in DISPROOF.md
--   - reading: the norm subscript is not separately defined in the source → the brief’s convention ||x||_M = sqrt(xᵀMx), hence inverse weight in the printed SDP; reason: this is the reading explicitly required by the structured brief; if the subscript denotes the inverse metric instead, the proposed norm repair is a notation clarification and this counterexample does not apply
--   - encoding: infimum over t with auxiliary scalar, vector and matrix variables → IsGLB of the set of feasible t values, and explicit sample mean and population covariance equalities; reason: this retains all SDP variables without accidental real-infimum defaults; bounded box support makes the admissible VaR supremum genuine
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 12 and (36), p. 27; Theorem 11 region, p. 26; EC.1.7, (EC.12)–(EC.14), pp. ec8–ec9 (PDF 46–47)

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Supplement_DY

open MeasureTheory
open scoped ENNReal

namespace DataDrivenRO.Guarantee.Supplement

/-- Under the brief's norm convention sqrt(xᵀMx), the printed SDP of Theorem 12
has a feasible value strictly smaller than both a point of (36) and an admissible VaR.
All moment data are nondegenerate and the empirical law is in the confidence region. -/
theorem theorem_12_counterexample :
    let lo : Fin 1 → ℝ := fun _ => -2
    let hi : Fin 1 → ℝ := fun _ => 2
    let mu : Fin 1 → ℝ := fun _ => 0
    let Sigma : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => 4)
    let C : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => 1 / 2)
    let S : Fin 2 → (Fin 1 → ℝ) := fun j _ => if j = 0 then -2 else 2
    let Phat : Measure (Fin 1 → ℝ) :=
      (1 / 2 : ℝ≥0∞) • Measure.dirac (S 0) +
      (1 / 2 : ℝ≥0∞) • Measure.dirac (S 1)
    let P : Measure (Fin 1 → ℝ) := Measure.dirac (fun _ => (1 / 2 : ℝ))
    let U := UDY lo hi mu Sigma C (1 / 16) 1 (999 / 1000)
    Sigma.PosDef ∧ C.transpose * C = Sigma⁻¹ ∧
    (∀ i, (∑ j, S j i) / 2 = mu i) ∧
    (∀ i j, (∑ k, (S k i - mu i) * (S k j - mu j)) / 2 = Sigma i j) ∧
    Phat ∈ regionDY lo hi mu Sigma (1 / 16) 1 ∧
    P ∈ regionDY lo hi mu Sigma (1 / 16) 1 ∧
    (fun _ => (1 / 2 : ℝ)) ∈ U ∧ U.Nonempty ∧ IsCompact U ∧ Convex ℝ U ∧
    (1 / 2 : ℝ) ≤ RobustMDP.Shared.supportFunction U (fun _ => 1) ∧
    DataDrivenRO.Guarantee.VaR P (999 / 1000) (fun _ => 1) = 1 / 2 ∧
    (190 / 999 : ℝ) ∈ sdpPrinted lo hi mu Sigma (1 / 16) 1 (999 / 1000) (fun _ => 1) ∧
    (190 / 999 : ℝ) < 1 / 2 ∧
    ¬ IsGLB (sdpPrinted lo hi mu Sigma (1 / 16) 1 (999 / 1000) (fun _ => 1))
      (RobustMDP.Shared.supportFunction U (fun _ => 1)) ∧
    ¬ IsGLB (sdpPrinted lo hi mu Sigma (1 / 16) 1 (999 / 1000) (fun _ => 1))
      (sSup ((fun Q : Measure (Fin 1 → ℝ) =>
        DataDrivenRO.Guarantee.VaR Q (999 / 1000) (fun _ => 1)) ''
        regionDY lo hi mu Sigma (1 / 16) 1)) := by sorry

end DataDrivenRO.Guarantee.Supplement
