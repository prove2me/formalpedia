-- Prove2me | Theorems.Thm_ConformalRiskControl_nonmonotone_counterexample
-- name    : ConformalRiskControl.nonmonotone_counterexample
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:14:23.687445+00:00
-- url     : https://prove2.me/theorems/90e5384a-cdd2-4005-a9e7-777f20f46a12
-- title:
--   Proposition 1 (as proved): without monotonicity the risk can be arbitrarily close to $B$
-- statement:
--   Let $n\ge1$, $\alpha<B$ with $\alpha>B/(n+1)$, and $\epsilon>0$. Then there are a probability space and exchangeable random functions $L_1,\dots,L_{n+1}$ on $\Lambda=[0,1]$ with the following properties. Every realisation is right-continuous, takes values in $[0,B]$ and satisfies $L_i(1)\le\alpha$. At least one realisation is not non-increasing. The test loss $L_{n+1}(\hat\lambda)$ at the conformal risk control parameter $\hat\lambda$ of eq. (4) is a random variable (measurable), and
--   $$\mathbb{E}\big[L_{n+1}(\hat\lambda)\big]\ge B-\epsilon.$$
--
--   So Theorem 1 fails without monotonicity, by an amount arbitrarily close to the largest possible.
--
--   **Formalization Note** The printed statement fixes neither $n$ nor $\alpha$. The proof (with $B=1$ after rescaling) assumes $\alpha\in(B/(n+1),B)$ and constructs i.i.d. piecewise-constant losses on $[0,1]$. The statement is made for that range, with the properties the construction provides. Measurability of the test loss is required explicitly so that the expectation is the genuine one.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Section 2.4, Proposition 1, p. 5; proof in Appendix B, p. 17

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem nonmonotone_counterexample (n : ℕ) (hn : 0 < n) (B α ε : ℝ)
    (hα₁ : B / (n + 1) < α) (hα₂ : α < B) (hε : 0 < ε) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (L : Fin (n + 1) → Ω → ℝ → ℝ),
      IsExchangeable P (Set.Icc 0 1) L ∧
      (∀ i ω, IsRightContOn (Set.Icc 0 1) (L i ω)) ∧
      (∀ i ω, LossBounds (Set.Icc 0 1) B α (L i ω) ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ L i ω x) ∧
      (∃ i ω, ¬ AntitoneOn (L i ω) (Set.Icc 0 1)) ∧
      Measurable (fun ω =>
        L (Fin.last n) ω (lhat (Set.Icc 0 1) B α (fun i : Fin n => L i.castSucc ω))) ∧
      ((B - ε : ℝ) : EReal) ≤
        upperExp P B (fun ω =>
          L (Fin.last n) ω (lhat (Set.Icc 0 1) B α (fun i : Fin n => L i.castSucc ω))) := by sorry

end ConformalRiskControl
