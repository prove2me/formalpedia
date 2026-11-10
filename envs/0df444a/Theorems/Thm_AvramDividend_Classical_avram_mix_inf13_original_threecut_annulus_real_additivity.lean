-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf13_original_threecut_annulus_real_additivity
-- name    : AvramDividend.Classical.avram_mix_inf13_original_threecut_annulus_real_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T12:27:12.890659+00:00
-- url     : https://prove2.me/theorems/278f17b6-51cd-49a7-8096-6448f9f5420e
-- title:
--   Original physical counts of adjacent negative annuli sum in real values
-- statement:
--   For the original same-sample-space, same-law spectrally negative Levy process, and any finite horizon and three ordered reciprocal cutoffs n ≤ m ≤ p, the original real jump count on annulus n-to-p is exactly the sum of original counts on adjacent annuli n-to-m and m-to-p. This uses Proved original nested cutoff count additivity and finite pathwise marked count without a finite global jump-variation or first absolute-moment assumption. It is a necessary identity for polarising the newly Proved original annulus L2 variance into disjoint-mark same-horizon cross moments, enabling the physical weighted small-jump strip isometry used by the mixed infinite-activity positive-clock reward theorem f5e6e083.
-- source:
--   Proved original nested cutoff additivity f0104cbc, full cutoff count finite-card f0197436, annulus pathwise finiteness 0060f5ce, and Proved annulus physical L2 variance 6e234a3f. Consumer is adjacent-annulus orthogonality then original weighted strip isometry and f5e6e083.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf13_original_threecut_annulus_real_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) :
    let A : ℕ → ℕ → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioc (-(1 / ((a : ℝ) + 1)))
          (-(1 / ((b : ℝ) + 1))))
    ∀ ω, (A n p ω).toReal =
      (A n m ω).toReal + (A m p ω).toReal := by sorry
