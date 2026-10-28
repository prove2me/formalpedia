-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_prefix_survival_concat
-- name    : AvramDividend.Classical.firstRecord_prefix_survival_concat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:09:19.797695+00:00
-- url     : https://prove2.me/theorems/b34816aa-4098-4590-b16a-9018d6464756
-- title:
--   Past record survival and shifted future survival concatenate to global drawdown survival
-- statement:
--   At a finite attained strict record u, suppose reflected drawdown stays at most a before u and the shifted post-u path has drawdown at most a throughout the interval [0,T]. Then the original reflected path stays at most a at every time before u+T. This deterministic concatenation bridges stopped-past survival with a purely future-path reward and feeds the strict first-upcrossing-before-ruin theorem in the killed-record renewal step.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, strong Markov survival concatenation at record stopping times.

import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstRecord_shifted_drawdown_survival_iff

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.firstRecord_prefix_survival_concat
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (a : ℝ) (T : ℝ≥0)
    (hPre : ∀ r : ℝ≥0, r < u → reflectedSup X r ω ≤ a)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    ∀ r : ℝ≥0, r < u + T → reflectedSup X r ω ≤ a := by sorry
