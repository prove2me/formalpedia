-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_shift
-- name    : FiniteEnergyPlane.expDecayCInfty_comp_shift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T21:43:46.891063+00:00
-- url     : https://prove2.me/theorems/8d775684-853b-4b55-8e38-9304da46c458
-- title:
--   Exponential C-infinity decay on an end is preserved by near-translations of the cylinder
-- statement:
--   Let $F$ be a real normed space, $f : \mathbb{R}\times\mathbb{R} \to F$ decaying like $e^{-b's}$ in $C^\infty$ on the end $s \to +\infty$ ($b' \in \mathbb{R}$ arbitrary), and $E : \mathbb{R}\times\mathbb{R} \to \mathbb{R}\times\mathbb{R}$ decaying like $e^{-bs}$ in $C^\infty$ with $b > 0$. Then for every $c \in \mathbb{R}^2$ the map $p \mapsto f(p + c + E(p))$ decays like $e^{-b's}$ in $C^\infty$.
--
--   Role: transfers $C^\infty$ decay through a change of cylindrical coordinates that is exponentially close to a translation (a rescaling and rotation at the puncture).
--
--   Formalization Note: decay is `ExpDecayCInfty f b'`; the rate $b'$ may be negative (growth bounds).
-- source:
--   Standard calculus of exponential decay on cylindrical ends; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff Real

/-- Exponential `C^∞` decay on a cylindrical end is preserved under composition on the right with a
map exponentially close to a translation: if `f` decays like `e^{-b's}` (any real `b'`) and `E`
decays like `e^{-bs}` with `b > 0`, then `p ↦ f (p + c + E p)` decays like `e^{-b's}`. -/
theorem expDecayCInfty_comp_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × ℝ → F) (b' : ℝ) (hf : ExpDecayCInfty f b')
    (E : ℝ × ℝ → ℝ × ℝ) (b : ℝ) (hb : 0 < b) (hE : ExpDecayCInfty E b) (c : ℝ × ℝ) :
    ExpDecayCInfty (fun p => f (p + c + E p)) b' := by
  sorry

end FiniteEnergyPlane
