-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_mono
-- name    : FiniteEnergyPlane.expDecayCInfty_mono
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-15T16:08:36.532025+00:00
-- url     : https://prove2.me/theorems/eabd8076-5355-4449-9f5b-3b0c4f8400a5
-- title:
--   Exponential C-infinity decay at a rate implies decay at every smaller rate
-- statement:
--   Let $F$ be a real normed space and $f:\mathbb R\times\mathbb R\to F$. If $f$ decays like $e^{-bs}$ in $C^\infty$ on the end $s\to+\infty$ (smooth on some $(s_1,\infty)\times\mathbb R$, and for every $m$ there are $C,s_2$ with $\|D^mf(s,t)\|\le Ce^{-bs}$ for $s\ge s_2$ and all $t$) and $b'\le b$, then $f$ decays like $e^{-b's}$ in $C^\infty$.
--
--   This lets several decay statements with different rates be combined at their common minimum rate.
--
--   Formalization Note: decay is `ExpDecayCInfty f b`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `C^∞` exponential decay at rate `b` implies `C^∞` exponential decay at every smaller rate
`b' ≤ b`. -/
theorem expDecayCInfty_mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {b b' : ℝ} (hf : ExpDecayCInfty f b) (hbb : b' ≤ b) :
    ExpDecayCInfty f b' := by
  sorry

end FiniteEnergyPlane
