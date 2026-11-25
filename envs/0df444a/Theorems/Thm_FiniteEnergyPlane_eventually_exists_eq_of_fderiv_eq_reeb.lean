-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eventually_exists_eq_of_fderiv_eq_reeb
-- name    : FiniteEnergyPlane.eventually_exists_eq_of_fderiv_eq_reeb
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T12:47:45.204582+00:00
-- url     : https://prove2.me/theorems/a404dd82-1042-5279-973b-33d3b1626608
-- title:
--   Reeb trajectories cross a positive family monotonically
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $F:\mathbb{R}\times\mathbb{C}\to\mathbb{R}^4$ a map that is $C^1$ at $p=(d,z)$, takes values in $S$ near $p$ and has injective derivative at $p$, with $DF(p)(c,v)=R(F(p))$ for some $c>0$. Let $y$ be a Reeb trajectory with $y(b)=F(p)$ and $N$ a neighbourhood of $p$. For all $s>b$ close to $b$ there is $q\in N$ with first coordinate greater than $d$ and $F(q)=y(s)$, and for all $s<b$ close to $b$ there is $q\in N$ with first coordinate less than $d$ and $F(q)=y(s)$.
--
--   Reusable for transition maps between families of leaves transverse to the Reeb flow.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A Reeb trajectory through a point of an immersed family positive against the Reeb field passes to later parameters in positive time and to earlier parameters in negative time. -/
theorem eventually_exists_eq_of_fderiv_eq_reeb (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (F : ℝ × ℂ → V 1) (p : ℝ × ℂ) (hF : ContDiffAt ℝ 1 F p)
    (hFS : ∀ᶠ q in 𝓝 p, F q ∈ energySurface H) (hinj : Function.Injective (fderiv ℝ F p))
    (c : ℝ) (hc : 0 < c) (v : ℂ) (hcv : fderiv ℝ F p (c, v) = reeb H (F p))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (b : ℝ) (hb : y b = F p)
    (N : Set (ℝ × ℂ)) (hN : N ∈ 𝓝 p) :
    (∀ᶠ s in 𝓝[>] b, ∃ q ∈ N, p.1 < q.1 ∧ F q = y s) ∧
      ∀ᶠ s in 𝓝[<] b, ∃ q ∈ N, q.1 < p.1 ∧ F q = y s := by
  sorry

end FiniteEnergyPlane
