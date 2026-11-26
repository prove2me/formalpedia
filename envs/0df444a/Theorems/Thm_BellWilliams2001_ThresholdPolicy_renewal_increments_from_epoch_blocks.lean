-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_increments_from_epoch_blocks
-- name    : BellWilliams2001.ThresholdPolicy.renewal_increments_from_epoch_blocks
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:07:15.447881+00:00
-- url     : https://prove2.me/theorems/95136d36-cd73-5957-bb9e-298c3f23b784
-- title:
--   Uniform renewal-count increment bounds from sliding epoch blocks
-- statement:
--   If all blocks of m consecutive epochs up to the deterministic cutoff have total duration within a relative error δ of m, then each centered inverse-count increment on [0,H] is at most 2δ times its duration plus 2m in absolute value. The cutoff exceeds twice the horizon and is a multiple of m.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Appendix A, inverse count representation (178)–(179)

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open Set Filter

namespace BellWilliams2001.ThresholdPolicy

theorem renewal_increments_from_epoch_blocks (e : ℕ → ℝ) (he : StrictMono e) (he0 : e 0 = 0)
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hmN : m ∣ N)
    (H : ℝ) (hH : 0 ≤ H) (hN : 2*H < (N:ℝ))
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hBlock : ∀ j ≤ N, |e (j+m) - e j - (m:ℝ)| ≤ δ*m) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ H →
      |((renewalCount e t).toNat:ℝ) - ((renewalCount e s).toNat:ℝ) - (t-s)| ≤
        2*δ*(t-s)+2*m := by sorry

end BellWilliams2001.ThresholdPolicy
