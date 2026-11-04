-- Prove2me | Theorems.Thm_FalconerPath_radial_lp
-- name    : FalconerPath.radial_lp
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:35.566217+00:00
-- url     : https://prove2.me/theorems/f1984ca4-b6b6-404b-9831-30deae85c666
-- title:
--   Radial $L^p$ densities and compact good-pin restrictions
-- statement:
--   Let $h\ge1$, $0<\varepsilon<\min(h,1)$, and let $\alpha,\beta$ be probabilities on $\mathbb R^{h+1}$ whose supports are bounded and positively separated. Assume $I_{h+\varepsilon}(\alpha),I_{h+\varepsilon}(\beta)<\infty$. There is a common $p>1$ and jointly Borel measurable nonnegative functions $F(x,w),H(y,w)$ such that $(\pi_x)_\#\alpha=F(x,\cdot)\sigma$ for $\beta$-almost every $x$ and $(\pi_y)_\#\beta=H(y,\cdot)\sigma$ for $\alpha$-almost every $y$, where $\pi_x(y)=(y-x)/|y-x|$ on these separated supports and $\sigma=\mathcal H^h|_{S^h}$. Both $\int\int F^p\,d\sigma\,d\beta$ and $\int\int H^p\,d\sigma\,d\alpha$ are finite.
--
--   There are compact $K_\alpha\subset\operatorname{supp}\alpha$ and $K_\beta\subset\operatorname{supp}\beta$ of positive respective masses and $L>0$ such that the normalized restrictions $\alpha^\prime,\beta^\prime$ have jointly measurable nonnegative radial densities in both orientations whose $p$th power surface integrals are at most $L$ at every pin in the corresponding restricted support. The Lean bound is on the $p$th power integral and makes the distinction between initial almost-everywhere densities and final every-support-pin bounds explicit.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.2, Lemma 5.7 (Radial $L^p$ estimate), label prep:radial-lp, including its final compact-restriction conclusion. The paper proves this version and describes it as an adaptation of Orponen2019, Section 3 and the proof of Theorem 1.13.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem radial_lp {h : ℕ} (hh : 1 ≤ h) (ε : ℝ)
    (hε : 0 < ε) (hεh : ε < min (h:ℝ) 1)
    (α β : Measure (Space (h+1))) (hα : Probability α) (hβ : Probability β)
    (hsep : HasBoundedSeparated β α)
    (hIα : energy ((h:ℝ)+ε) α < ∞) (hIβ : energy ((h:ℝ)+ε) β < ∞) :
    ∃ p : ℝ, 1 < p ∧ RadialLp β α p ∧
      ∃ Kα Kβ : Set (Space (h+1)), IsCompact Kα ∧ IsCompact Kβ ∧
        Kα ⊆ α.support ∧ Kβ ⊆ β.support ∧ 0 < α Kα ∧ 0 < β Kβ ∧
        ∃ L : ℝ, 0 < L ∧ UniformRadialLp
          (normalizedRestriction β Kβ) (normalizedRestriction α Kα) p L := by sorry
end FalconerPath
