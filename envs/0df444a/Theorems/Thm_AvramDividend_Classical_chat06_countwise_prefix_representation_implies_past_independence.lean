-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_countwise_prefix_representation_implies_past_independence
-- name    : AvramDividend.Classical.chat06_countwise_prefix_representation_implies_past_independence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:55:29.460617+00:00
-- url     : https://prove2.me/theorems/d4371de9-38a9-4146-b689-fbe39f177cd4
-- title:
--   Whole-future independence from a past event represented countwise by measurable interarrival prefixes
-- statement:
--   Suppose that, on every count cylinder N=n, a measurable observed-past event H is almost surely representable by a measurable event of an earlier-arrival prefix Z_n. If the residual wait and complete future jointly factor against every such prefix event on each count cylinder, then their randomly selected counterparts jointly factor against H itself. The proof transports the countwise factorisation through almost-sure event equality and applies the accepted countwise gluing theorem. This isolates, rather than assumes away, the mathematical obligation to represent actual Poisson natural-filtration events by earlier waiting-time prefixes.
-- source:
--   Source bv_countwise_prefix_representation_implies_past_independence_chat06_20261021.lean, 64 lines, 2637 bytes, SHA-256 5c44433a13b69f50d83a88da958c8ba3f476070a05e80144849f46f8648ea24a; private probe 0463a3c0-71d2-490e-9d40-7291126b9b19 reached sentinel with no candidate errors.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_chat06_selected_past_residual_future_joint_countwise_gluing

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_countwise_prefix_representation_implies_past_independence
    {Ω E A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace A]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (Z : ℕ → Ω → A)
    (H : Set Ω) (hH : MeasurableSet H)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (G : ℕ → Ω → E) (hG : ∀ n, Measurable (G n))
    (B : Set E) (hB : MeasurableSet B)
    (u : ℝ) (c d : ℝ≥0∞)
    (hRep : ∀ n : ℕ, ∃ Q : Set A,
      MeasurableSet Q ∧
      (fun ω : Ω => ω ∈ H ∧ N ω = n) =ᵐ[P]
        (fun ω : Ω => Z n ω ∈ Q ∧ N ω = n))
    (hPrefixFactor : ∀ n (Q : Set A), MeasurableSet Q →
      P {ω | Z n ω ∈ Q ∧ N ω = n ∧
        u < F n ω ∧ G n ω ∈ B} =
        (P {ω | Z n ω ∈ Q ∧ N ω = n} * c) * d) :
    P {ω | ω ∈ H ∧ u < F (N ω) ω ∧
      G (N ω) ω ∈ B} = (P H * c) * d := by sorry
