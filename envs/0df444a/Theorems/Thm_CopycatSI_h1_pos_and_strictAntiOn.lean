-- Prove2me | Theorems.Thm_CopycatSI_h1_pos_and_strictAntiOn
-- name    : CopycatSI.h1_pos_and_strictAntiOn
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:47:10.363992+00:00
-- url     : https://prove2.me/theorems/cc78e77d-92cc-43cb-9a5f-d852ccc73ca1
-- title:
--   Proposition 2(ii), cutoff clause — $h_1(\beta)>0$ for $\beta<\beta^*$, and $h_1$ is decreasing on $[0,\beta^*]$
-- statement:
--   Let $\beta^*=(\sqrt{73}-5)/6$ and
--   $$
--   h_1(\beta)=\frac{1-\beta}{(2-\beta)(4-3\beta)}\Bigl(2-\beta-\frac{\beta}{2}\sqrt{\frac{17-13\beta}{1-\beta}}\Bigr).
--   $$
--   Then
--
--   1. $h_1(\beta)>0$ for every $0\le\beta<\beta^*$, and
--   2. $h_1$ is strictly decreasing on $[0,\beta^*]$.
--
--   Since $h_1$ is the holding cost below which the retailer carries strategic inventory under the dynamic contract, this says that more competitive copycats shrink the range of holding costs at which strategic inventory survives, and that the range is nonempty for every $\beta<\beta^*\approx 0.59$.
--
--   Differences from the source:
--   - encoding: "h₁ > 0 for all β < (√73 − 5)/6" → for all 0 ≤ β < β*; reason: β ≥ 0 is the model's domain (copycat valuation βθ, p.6); there are no other instances
--   - reading: "h₁ is decreasing in β" → h₁ is strictly decreasing on [0, β*]; reason: β* is where h₁ reaches 0 and stops being a cutoff; the formula is not monotone on [0, 1); strict decrease is the stronger reading
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), Proposition 2(ii), last sentence, p.9; h₁ and β* from Table 2, Condition I, p.9

import Mathlib
import Definitions.Def_CopycatSI_Model
import Definitions.Def_CopycatSI_Game
import Definitions.Def_CopycatSI_ClosedForms

namespace CopycatSI

/-- **Proposition 2(ii), the cutoff clause** (Jin–Wu–Chen, SSRN 3826955, version of 2023-05-17,
p.9): "the cutoff `h₁ > 0` for all `β < (√73 − 5)/6` and `h₁` is decreasing in `β`".
For every `0 ≤ β < β*`, `h₁(β) > 0`; and `h₁` is strictly decreasing on `[0, β*]`.

**Formalization Note** `β ≥ 0` is the model's domain. "Decreasing" is read as strictly
decreasing on `[0, β*]`, the range in which `h₁` is the cutoff. -/
theorem h1_pos_and_strictAntiOn :
    (∀ β : ℝ, 0 ≤ β → β < betaStar → 0 < h1 β) ∧
    StrictAntiOn h1 (Set.Icc 0 betaStar) := by sorry

end CopycatSI
