-- Prove2me | Theorems.Thm_FiniteEnergyPlane_bounded_iteratedFDeriv_endA_endW
-- name    : FiniteEnergyPlane.bounded_iteratedFDeriv_endA_endW
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T19:14:45.095651+00:00
-- url     : https://prove2.me/theorems/3b8738d6-ecc1-4b32-babf-03a045e4aecf
-- title:
--   Bounded derivatives of the end coordinates of a curve with exponential asymptotics
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $P=(x,T)$ a periodic Reeb orbit on $S$, and $f:\mathbb{C}\to\mathbb{R}^4$. On the end $z=e^{2\pi(s+it)}$ write $a(s,t)=\mathrm{aCoord}(f(z))$ and $w(s,t)=\mathrm{proj}(f(z))$. Assume that $a(s,t)-Ts-d_f$ and $w(s,t)-x(Tt+c_f)$ decay exponentially in $C^\infty$ at a rate $b_f>0$ (`ExpDecayCInfty`). Then for every $m\ge1$ the $m$-th derivative of $(s,t)\mapsto(a(s,t),w(s,t))$ is bounded for large $s$, uniformly in $t$.
--
--   These are the $C^\infty$ bounds on the end coordinates $(a,w)$ of a curve asymptotic to $P$, used when comparing such a curve with tube coordinates around $P$.
--
--   **Formalization Note** `endA H f cylInf` and `endW H f cylInf` are the coordinates $a$ and $w$ along the end `cylInf s t`. The bound is on `iteratedFDeriv ℝ m` of the pair at `(s, t)` for `s ≥ s₁`, for each `m ≥ 1`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379; setting of C. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012)

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Bounded derivatives of the end coordinates. If `f` has exponential `C^∞` asymptotics at the
periodic Reeb orbit `P` along the end `cylInf` (`hfa`, `hfw`), then every derivative of order
`m ≥ 1` of `(s, t) ↦ (endA f (s, t), endW f (s, t))` is bounded for large `s`, uniformly in `t`. -/
theorem bounded_iteratedFDeriv_endA_endW (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (f : ℂ → V 1) (df cf bf : ℝ)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (hbf : 0 < bf) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => (endA H f cylInf p, endW H f cylInf p)) (s, t)‖
        ≤ C := by
  sorry

end FiniteEnergyPlane
