-- Prove2me | Theorems.Thm_DarkKnights_footnote_13
-- name    : DarkKnights.footnote_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:56.946442+00:00
-- url     : https://prove2.me/theorems/00a986e2-9d7a-42de-9243-9246882d7c4e
-- title:
--   Footnote 13 — in the active-CDS-buyer model $h^*=1$ for $b\le Zk^\alpha/2$
-- statement:
--   In the active-CDS-buyer model, let $\alpha\in(0,1)$, $Z>0$, $k>0$ and $0\le b\le Zk^\alpha/2$. Then
--
--   1. if $b>0$, the value of debt $h\mapsto M(k,b,h)$ is strictly increasing on $[0,1]$;
--   2. $h=1$ maximizes $M(k,b,h)$ over $h\in[0,1]$.
--
--   Full hedging maximizes the lender's value whenever the face value is at most half the largest asset value, which is the case at the optimal debt (8).
--
--   Differences from the source:
--   - reading: $\partial M/\partial h$ is positive for all $h\in[0,1]$ → $M$ strictly increasing on $[0,1]$ when $b>0$; reason: at $b=Zk^\alpha/2$ the derivative vanishes at the single point $h=1$ and at $b=0$ everywhere; strict monotonicity is what the footnote uses
--   - encoding: the derivative of $M$, with denominator $Zk^\alpha$ → hypothesis $k>0$; reason: the expression is undefined at $k=0$
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §1, p.12 (PDF 14), 'the optimal hedge ratio is h∗ = 1' and footnote 13

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveBuyerModel

namespace DarkKnights

/-- **Footnote 13** (the lender fully hedges in the active-CDS-buyer model).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §1, p.12 (PDF p.14): "one can show that the optimal hedge ratio is
h∗ = 1", with footnote 13, p.12.

For `k > 0` and `0 ≤ b ≤ Z k^α/2`:
1. if `b > 0`, the value of debt `h ↦ M(k, b, h)` of model 1 is strictly increasing on `[0, 1]`;
2. `h = 1` maximizes `M(k, b, h)` over `h ∈ [0, 1]`.

**Formalization Note** "∂M/∂h is positive for all h ∈ [0, 1]" is stated as strict monotonicity
on `[0, 1]` (at `b = Z k^α/2` the derivative vanishes at the single point `h = 1`; at `b = 0`
the value of debt is identically `0`). -/
theorem footnote_13 (α Z k b : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hk : 0 < k)
    (hb : 0 ≤ b) (hbZ : b ≤ Z * k ^ α / 2) :
    (0 < b → StrictMonoOn (fun h => debtValue1 α Z k b h) (Set.Icc (0 : ℝ) 1)) ∧
      ∀ h ∈ Set.Icc (0 : ℝ) 1, debtValue1 α Z k b h ≤ debtValue1 α Z k b 1 := by sorry

end DarkKnights
