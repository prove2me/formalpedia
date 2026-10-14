-- Prove2me | Theorems.Thm_DbarRegularity_dbar_sobolev_estimate
-- name    : DbarRegularity.dbar_sobolev_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:55:41.653664+00:00
-- url     : https://prove2.me/theorems/47a9eb3f-974d-4a4e-af8f-5c5ed83477c0
-- title:
--   The W^{k,p} estimate for the Cauchy–Riemann operator on a disc
-- statement:
--   Let $k\ge1$ be an integer, $p>1$ and $R>0$. Then there is a constant $M=M(k,p,R)$ such that for every disc $B\subset\mathbb{C}$ of radius $R$ and every smooth map $\varphi:\mathbb{C}\to\mathbb{C}^n$ whose support lies in the interior of $B$,
--   $$\|\varphi\|_{W^{k,p}(B)}\le M\,\|\bar\partial\varphi\|_{W^{k-1,p}(B)} .$$
--   Here $\bar\partial\varphi=\partial\varphi/\partial s+i\,\partial\varphi/\partial t$ for $z=s+it$, and $\|\psi\|_{W^{k,p}(B)}=\sum_{j=0}^{k}\|D^j\psi\|_{L^p(B)}$ is the Sobolev norm of the definition module.
--
--   This is the elliptic estimate for $\bar\partial$ that Hofer–Wysocki–Zehnder use to bound the derivatives of pseudoholomorphic half-cylinders, and the basic a priori estimate of the regularity theory of pseudoholomorphic curves.
--
--   **Formalization Note** `ContDiff ℝ ∞ φ` is $C^\infty$ smoothness over $\mathbb{R}$ (not analyticity). $\varphi_s$ and $\varphi_t$ are `fderiv ℝ φ z 1` and `fderiv ℝ φ z Complex.I`, and $\bar\partial\varphi$ is `dbar φ`. $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`. "Support in the interior of $B$" is `tsupport φ ⊆ ball c R`. The norms are `sobolevNorm k (ENNReal.ofReal p) (ball c R)`, valued in `ℝ≥0∞`; any other choice of equivalent $W^{k,p}$ norm changes only $M$. The constant `M : ℝ≥0` is chosen before the centre $c$ of the disc and before $\varphi$, and it may depend on $n$. Hofer–Wysocki–Zehnder take $\varphi$ with values in $\mathbb{R}^2$ and $\bar\partial=\partial_s+J_0\partial_t$ with $J_0^2=-1$; identifying $\mathbb{R}^2$ with $\mathbb{C}$ so that $J_0$ is multiplication by $i$ gives the case $n=1$, and the statement here allows $\mathbb{C}^n$, as in Abbas–Hofer, § 4.2.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13(3) (1996) 337–379, http://www.numdam.org/item/AIHPC_1996__13_3_337_0/, estimate (49), p. 366, § 3

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Hofer–Wysocki–Zehnder, *Properties of pseudoholomorphic curves in symplectisations I*, estimate (49)
(p. 366): for an integer `k ≥ 1`, `p > 1` and `R > 0` there is `M = M(k, p, R)` such that for
every disc `B` of radius `R` and every smooth `φ : ℂ → ℂⁿ` with support in the interior of `B`,
`‖φ‖_{W^{k,p}(B)} ≤ M ‖∂̄φ‖_{W^{k-1,p}(B)}`. -/
theorem dbar_sobolev_estimate (n k : ℕ) (p R : ℝ) (hk : 1 ≤ k) (hp : 1 < p) (hR : 0 < R) :
    ∃ M : ℝ≥0, ∀ (c : ℂ) (φ : ℂ → EuclideanSpace ℂ (Fin n)), ContDiff ℝ ∞ φ →
      tsupport φ ⊆ ball c R →
      sobolevNorm k (ENNReal.ofReal p) (ball c R) φ
        ≤ M * sobolevNorm (k - 1) (ENNReal.ofReal p) (ball c R) (dbar φ) := by sorry

end DbarRegularity
