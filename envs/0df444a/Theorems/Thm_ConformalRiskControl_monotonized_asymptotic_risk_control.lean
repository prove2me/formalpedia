-- Prove2me | Theorems.Thm_ConformalRiskControl_monotonized_asymptotic_risk_control
-- name    : ConformalRiskControl.monotonized_asymptotic_risk_control
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:18:58.950802+00:00
-- url     : https://prove2.me/theorems/4a2ca2ae-83bd-4119-87f5-10a66e7f7aec
-- title:
--   Theorem A.1 (as proved): asymptotic risk control for non-monotone losses
-- statement:
--   Let $\Lambda\subset\mathbb{R}$ be nonempty and compact with $\lambda_{\max}=\max\Lambda$, and let $\alpha<B$. Let $L_1,L_2,\dots$ be i.i.d. random functions on $\Lambda$ with right-continuous, possibly non-monotone, realisations. Assume that almost surely, for every $i$:
--
--   1. $L_i$ is bounded below by a fixed constant;
--   2. $\sup_\lambda L_i(\lambda)\le B$;
--   3. $L_i(\lambda_{\max})\le\alpha$.
--
--   Let $\hat R_n^{\uparrow}(\lambda)=\sup_{t\ge\lambda}\hat R_n(t)$ and $\hat\lambda_n^{\uparrow}=\inf\{\lambda:\hat R_n^{\uparrow}(\lambda)\le\alpha\}$. Then
--   $$\limsup_{n\to\infty}\mathbb{E}\big[L_{n+1}(\hat\lambda_n^{\uparrow})\big]\le\alpha.$$
--
--   **Formalization Note** The paper writes $\lim$, but its proof bounds $\limsup$ by Fatou's lemma and does not show that the limit exists, so the statement is made for $\limsup$. Indices start at $0$: $\hat\lambda_n^{\uparrow}$ uses $L_0,\dots,L_{n-1}$ and is tested on $L_n$.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Appendix A, Theorem A.1, p. 15; proof in Appendix B, p. 17

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem monotonized_asymptotic_risk_control {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Λ : Set ℝ) (hΛ : IsCompact Λ)
    (hΛne : Λ.Nonempty) (B α : ℝ) (hαB : α < B) (L : ℕ → Ω → ℝ → ℝ) (hiid : IsIID P Λ L)
    (hrc : ∀ i ω, IsRightContOn Λ (L i ω)) (lo : ℝ) (hlo : ∀ᵐ ω ∂P, ∀ i, ∀ x ∈ Λ, lo ≤ L i ω x)
    (h5 : ∀ᵐ ω ∂P, ∀ i, LossBounds Λ B α (L i ω)) :
    limsup (fun n : ℕ => upperExp P B (fun ω => L n ω (lhatPlus Λ α (fun i : Fin n => L i ω))))
      atTop ≤ (α : EReal) := by sorry

end ConformalRiskControl
