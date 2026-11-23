-- Prove2me | Theorems.Thm_ConformalRiskControl_weighted_risk_control_covariate_shift
-- name    : ConformalRiskControl.weighted_risk_control_covariate_shift
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:16:19.333216+00:00
-- url     : https://prove2.me/theorems/aaa9cd77-fbec-450a-bb0c-2c0f83be6aed
-- title:
--   Proposition 2: weighted conformal risk control under covariate shift
-- statement:
--   Let $P_{\mathrm{train}}$ and $P_{\mathrm{test}}$ be probability measures on $\mathcal X\times\mathcal Y$. Let $w:\mathcal X\to[0,\infty)$ be measurable with
--   $$\frac{dP_{\mathrm{test}}}{dP_{\mathrm{train}}}(x,y)=w(x)$$
--   (covariate shift). Let $\Lambda\subset\mathbb{R}$ be nonempty and compact, $n\ge1$ and $\alpha<B$. Let $\ell:(\mathcal X\times\mathcal Y)\times\Lambda\to\mathbb{R}$ be such that $\ell(\cdot,\lambda)$ is measurable for every $\lambda$ and $\ell(z,\cdot)$ is non-increasing and right-continuous for every $z$. Assume that for $P_{\mathrm{train}}$-almost every $z$, $\ell(z,\cdot)$ takes values in $[0,B]$ and $\ell(z,\lambda_{\max})\le\alpha$. Let $(X_1,Y_1),\dots,(X_n,Y_n)\sim P_{\mathrm{train}}$ and $(X_{n+1},Y_{n+1})\sim P_{\mathrm{test}}$ be independent, and put $L_i=\ell((X_i,Y_i),\cdot)$. With the weighted parameter $\hat\lambda(x)$ of Section 4.1,
--   $$\mathbb{E}\big[L_{n+1}(\hat\lambda(X_{n+1}))\big]\le\alpha.$$
--
--   This generalizes weighted conformal prediction (Tibshirani et al., 2019) to monotone risks. The weight $w$ may be unbounded.
--
--   **Formalization Note** The covariate shift is encoded as $P_{\mathrm{test}}=w(x)\cdot P_{\mathrm{train}}$. The data are the product of $n$ copies of $P_{\mathrm{train}}$ and one copy of $P_{\mathrm{test}}$. The ratio in $\hat\lambda(x)$ is undefined only when all weights vanish, which happens with probability $0$ at $x=X_{n+1}$.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Section 4.1, Proposition 2, eqs. (9)-(10), p. 10; proof in Appendix B, p. 18

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem weighted_risk_control_covariate_shift {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (Ptr Pte : Measure (X × Y)) [IsProbabilityMeasure Ptr]
    [IsProbabilityMeasure Pte] (w : X → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hshift : Pte = Ptr.withDensity fun z => ENNReal.ofReal (w z.1))
    (n : ℕ) (hn : 0 < n) (Λ : Set ℝ) (hΛ : IsCompact Λ) (hΛne : Λ.Nonempty) (B α : ℝ)
    (hαB : α < B) (ℓ : X × Y → ℝ → ℝ) (hℓ : ∀ x ∈ Λ, Measurable fun z => ℓ z x)
    (hanti : ∀ z, AntitoneOn (ℓ z) Λ) (hrc : ∀ z, IsRightContOn Λ (ℓ z))
    (hbd : ∀ᵐ z ∂Ptr, LossBounds Λ B α (ℓ z) ∧ ∀ x ∈ Λ, 0 ≤ ℓ z x) :
    upperExp ((Measure.pi fun _ : Fin n => Ptr).prod Pte) B
        (fun D => ℓ D.2 (weightedLhat Λ B α w (fun i => ℓ (D.1 i)) (fun i => (D.1 i).1) D.2.1))
      ≤ (α : EReal) := by sorry

end ConformalRiskControl
