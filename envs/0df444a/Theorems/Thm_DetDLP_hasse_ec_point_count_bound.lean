-- Prove2me | Theorems.Thm_DetDLP_hasse_ec_point_count_bound
-- name    : DetDLP.hasse_ec_point_count_bound
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:25.980166+00:00
-- url     : https://prove2.me/theorems/79ea9443-edc1-40ca-a2f0-cac00da85995
-- title:
--   Hasse's Theorem for Elliptic Curves over Prime Fields
-- statement:
--   For every prime $p > 3$ and every elliptic curve $E/\mathbb{F}_p$, $|\#E(\mathbb{F}_p) - (p + 1)| \le 2\sqrt{p}$.
-- source:
--   Hasse's Theorem (cited in Section 3.1, eq. (3.2) & p. 9)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

/-- Hasse's theorem for elliptic curves over prime fields `F_p` (`p > 3`):
`|#E(F_p) - (p + 1)| ≤ 2 √p`. -/
theorem hasse_ec_point_count_bound :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        |(Fintype.card E.toAffine.Point : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) := by sorry

end DetDLP
