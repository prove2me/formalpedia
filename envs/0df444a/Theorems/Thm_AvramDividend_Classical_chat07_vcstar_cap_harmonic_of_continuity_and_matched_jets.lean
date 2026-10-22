-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_vcstar_cap_harmonic_of_continuity_and_matched_jets
-- name    : AvramDividend.Classical.chat07_vcstar_cap_harmonic_of_continuity_and_matched_jets
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:46:36.783986+00:00
-- url     : https://prove2.me/theorems/58d836e9-d201-4ded-a722-627af5024700
-- title:
--   Exact nonlocal dividend-value harmonicity at a positive barrier from continuity and matched jets
-- statement:
--   At a positive canonical barrier a, suppose the underlying scale function vanishes on negative reserves, is generator-integrable at a, and has generator residual continuous on (0,a] and zero in the interior. Suppose the dividend value vcstar W matches the normalised scale-function branch in first and second derivatives at a. Then vcstar W itself belongs to the full Lévy generator domain at a and satisfies Γvcstar(a)−q vcstar(a)=0. The proof composes accepted endpoint harmonicity, support branch agreement and left-germ generator congruence. This isolates the remaining stochastic and smooth-fit hypotheses and does not assume global optimality.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_vcstar_cap_harmonic_of_continuity_and_matched_jets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hsupport : ∀ z : ℝ, z < 0 → W z = 0)
    (a : ℝ) (ha : 0 < a) (hbarrier : a = (cstar W).toReal)
    (hdom : X.GeneratorIntegrable W a)
    (hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioc 0 a))
    (hinside : ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0)
    (hder : deriv (vcstar W) a =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W a)) a)
    (hsecond : iteratedDeriv 2 (vcstar W) a =
      iteratedDeriv 2
        (fun z : ℝ => divE (W z) (scaleDeriv W a)) a) :
    X.GeneratorIntegrable (vcstar W) a ∧
      X.generator (vcstar W) a - q * vcstar W a = 0 := by sorry
