-- Prove2me | Theorems.Thm_EndoRefLA_PartialPPE_value_continuous
-- name    : EndoRefLA.PartialPPE.value_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:52.673564+00:00
-- url     : https://prove2.me/theorems/d5da5ab6-f168-4fa9-a62b-20ed4d276f76
-- title:
--   Proof of Theorem 3, p. 34 — Λ ↦ V_λ(X*_ex(Λ)|B0) is finite and continuous on [1, ∞), and equals V_λ(X*_ex(λ)|B0) at λ∧λmax
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; the pricing kernel $\rho$ is a positive, integrable random variable; the initial wealth is $x_0>0$; the gain-loss weight is $\alpha>0$; the intrinsic degree of loss aversion is $\lambda\ge 1$; the utility $u$ satisfies Assumption 1; and the exogenous reference point $B_0\ge 0$ is measurable with $\mathbb E|u(B_0)|<\infty$.
--   Let $\nu_G,\nu_L$ satisfy their root equations, let $\lambda_{\max}$ be given by (6), and for each $\Lambda\ge1$ let $X^*_{\rm ex}(\Lambda)$ be an optimal solution of (4) with degree of loss aversion $\Lambda$. Then:
--   1. $V_\lambda(X^*_{\rm ex}(\Lambda)\mid B_0)>-\infty$ for every $\Lambda\ge1$;
--   2. the map $\Lambda\mapsto V_\lambda(X^*_{\rm ex}(\Lambda)\mid B_0)$ is continuous on $[1,\infty)$;
--   3. $V_\lambda(X^*_{\rm ex}(\lambda\wedge\lambda_{\max})\mid B_0)=V_\lambda(X^*_{\rm ex}(\lambda)\mid B_0)$.
--
--   Note that the evaluation uses the intrinsic degree of loss aversion $\lambda$, while $X^*_{\rm ex}(\Lambda)$ is optimal for $\Lambda$. Continuity together with part 3 gives the two endpoint values $f^{-1}_{B_0}(\underline c)$ and $f^{-1}_{B_0}(\bar c)$ used in Theorem 3.
--
--   **Formalization Note.** The value is finite (part 1), so continuity is stated for its real value. $\lambda\wedge\lambda_{\max}$ is $\lambda$ when $\lambda_{\max}=+\infty$.
-- source:
--   He & Strub, How Endogenization of the Reference Point Affects Loss Aversion: A Study of Portfolio Selection, SSRN 3318295 (version of May 4, 2022), p. 34 (PDF 34), proof of Theorem 3, continuity of Vλ(X*ex(Λ)|B0) in Λ ≥ 1 and the displayed limits

import Mathlib
import Definitions.Def_EndoRefLA_PartialPPE_Model

namespace EndoRefLA.PartialPPE

open MeasureTheory Filter Topology

/-- Proof of Theorem 3, p. 34: `V_λ(X*_ex(Λ)|B0)` is finite and continuous in `Λ ≥ 1`, and
`V_λ(X*_ex(λ ∧ λmax)|B0) = V_λ(X*_ex(λ)|B0)`. -/
theorem value_continuous
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Ω → ℝ) (x0 α lam : ℝ) (u : ℝ → ℝ) (u0 : EReal) (B0 : Ω → ℝ)
    (hρ : IsPricingKernel P ρ) (hx0 : 0 < x0) (hα : 0 < α) (hlam : 1 ≤ lam)
    (hu : Assumption1 P ρ u u0) (hB0 : IsRefPoint P u u0 B0)
    (νG νL : ℝ)
    (hνG : price P ρ B0 < ENNReal.ofReal x0 →
      0 < νG ∧ price P ρ (fun ω => max (Iinv u (νG * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (hνL : ENNReal.ofReal x0 < price P ρ B0 →
      0 < νL ∧ price P ρ (fun ω => min (Iinv u (νL * ρ ω)) (B0 ω)) = ENNReal.ofReal x0)
    (Xex : ℝ → Ω → ℝ) (hXex : ∀ Λ : ℝ, 1 ≤ Λ → IsOptEx P ρ x0 α u u0 B0 Λ (Xex Λ)) :
    (∀ Λ : ℝ, 1 ≤ Λ → V P α u u0 lam (Xex Λ) B0 ≠ ⊥) ∧
    ContinuousOn (fun Λ : ℝ => (V P α u u0 lam (Xex Λ) B0).toReal) (Set.Ici 1) ∧
    V P α u u0 lam (Xex (lamCap P ρ x0 α lam u B0 νG νL)) B0 = V P α u u0 lam (Xex lam) B0 := by sorry

end EndoRefLA.PartialPPE
