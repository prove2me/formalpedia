-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_compact_two_reserve_negative_mark_Taylor_abs_bound
-- name    : AvramDividend.Classical.avram_freshD_original_compact_two_reserve_negative_mark_Taylor_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T14:21:19.412181+00:00
-- url     : https://prove2.me/theorems/067125d6-b839-4ac0-8b44-4058b0771cd4
-- title:
--   Original C² compact-strip negative-mark Taylor differences admit a uniform bound independent of jump size and including infinite cap
-- statement:
--   A finite compact positive reserve strip [a,b] strictly inside the original C² generator domain, including when C=⊤, provides a deterministic uniform absolute bound on the difference of the two actual full negative-mark Taylor kernels evaluated at any u,y in that strip. The Proved top-cap-compatible absolute negative-mark value loss bound c1fc53f3 supplies K with |w(r+z)-w(r)|≤K uniformly for r∈[0,b] and all z<0, without assuming any moment of large negative jumps. The Proved C² compact-strip derivative bound 8e186779 supplies M with |w'(r)|≤M. For negative z, whenever the compensated Taylor derivative term is active (-1<z<0), |z|≤1, so its absolute value is ≤M. Each kernel therefore has absolute value ≤K+M, and the signed difference is ≤2(K+M). This proves the deterministic weight envelope required by the original chronological marked-grid signed positive-part expected limit without assuming finite C, global bounded derivatives, or arbitrary pathwise Gaussian control. Crucially, it does not claim the kernel difference itself vanishes across zero-landing marks.
-- source:
--   Original AvramDividend.Classical mixed Gaussian and negative Lévy mark full cash-excess 242ca5f1, compact band integrable envelope needed to apply exact chronological signed upperlim positive expectation bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_compact_negative_mark_loss_abs_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_compact_two_reserve_negative_mark_Taylor_abs_bound
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t < 0, w t = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C})
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C}) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ u ∈ Icc a b, ∀ y ∈ Icc a b, ∀ z : ℝ, z < 0 →
        |(w (u + z) - w u -
            (if -1 < z then z * deriv w u else 0)) -
          (w (y + z) - w y -
            (if -1 < z then z * deriv w y else 0))| ≤ L := by sorry
