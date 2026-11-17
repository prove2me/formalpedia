-- Prove2me | Theorems.Thm_AltRegret_Supplement_theorem_7
-- name    : AltRegret.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:11:08.541317+00:00
-- url     : https://prove2.me/theorems/3624baf1-bcc0-4994-b0d6-65027d13418a
-- title:
--   Theorem 7 — distributional alternating-regret bound
-- statement:
--   Let $X$ be a nonempty compact convex set, let $\mu$ be a Borel reference probability on $X$, and let $f_t:X\to[-1,1]$ be continuous and convex. For every horizon $T\ge1$ and every Borel probability $\rho\ll\mu$, continuous AA-Hedge with $\eta=1/8$ and $\beta=1/32$ satisfies
--   $$
--   \operatorname{Reg}_{\mathrm{Alt}}^T(\rho)
--     \le 8\,\mathrm{KL}(\rho\Vert\mu)+\frac{\operatorname{Var}_\rho(f_T)}4
--     \le 8\,\mathrm{KL}(\rho\Vert\mu)+\frac14.
--   $$
--   The bound allows $\mathrm{KL}(\rho\Vert\mu)=+\infty$ and retains both conclusions of the theorem.
--
--   It is the distributional estimate from which the pointwise OCO bound is derived.
--
--   Differences from the source:
--   - encoding: KL(ρ‖μ) is an extended nonnegative real → Mathlib's measure KL is cast to EReal; reason: this preserves +∞ and makes the displayed inequalities total without a finiteness assumption
--   - encoding: Algorithm 2 → any run satisfying the literal maximization, exponential reweighting, correction, and barycenter equations; reason: the relation represents every permitted choice of the algorithm
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Theorem 7, p.10

import Mathlib
import Definitions.Def_AltRegret_Supplement_ContinuousAAHedgeRun

open MeasureTheory ProbabilityTheory InformationTheory

namespace AltRegret.Supplement

/-- **Theorem 7 (Distributional alternating-regret bound).** Tao–Zheng,
*Optimal Alternating Regret for Online Learning and Games*, arXiv:2608.24731, Theorem 7,
p.10. Continuous AA-Hedge with `η=1/8`, `β=1/32` has distributional alternating regret
at most `8 KL(ρ‖μ) + Varρ(f_T)/4`, hence at most `8 KL(ρ‖μ)+1/4`.

**Formalization Note.** `InformationTheory.klDiv` is in nats and takes values in `ℝ≥0∞`;
casting it to `EReal` retains `+∞`, so no finiteness hypothesis is added. `ρ X = μ X = 1`
encodes `ρ, μ ∈ Δ_X`. Algorithm 2 is the literal update relation `ContinuousAAHedgeRun`. -/
theorem theorem_7 {d : ℕ} (X : Set (Point d)) (hXne : X.Nonempty)
    (hXcompact : IsCompact X) (hXconvex : Convex ℝ X)
    (f : ℕ → Point d → ℝ) (hf : IsOCOSequence X f)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] (hμX : μ X = 1)
    (run : ContinuousAAHedgeRun X μ f (1 / 8) (1 / 32))
    (T : ℕ) (hT : 1 ≤ T) (ρ : Measure (Point d)) [IsProbabilityMeasure ρ]
    (hρX : ρ X = 1) (hρμ : ρ ≪ μ) :
    ((distributionalAltRegret f run.play T ρ : ℝ) : EReal) ≤
        8 * (klDiv ρ μ : EReal) + (varianceUnder ρ (f T) : EReal) / 4 ∧
      ((distributionalAltRegret f run.play T ρ : ℝ) : EReal) ≤
        8 * (klDiv ρ μ : EReal) + 1 / 4 := by sorry

end AltRegret.Supplement
