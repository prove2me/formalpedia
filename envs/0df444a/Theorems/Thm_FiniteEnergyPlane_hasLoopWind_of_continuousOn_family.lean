-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_continuousOn_family
-- name    : FiniteEnergyPlane.hasLoopWind_of_continuousOn_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T11:07:56.0999+00:00
-- url     : https://prove2.me/theorems/6d46a231-1d17-4001-a21d-1ff04306a515
-- title:
--   Homotopy invariance of the winding number of a family of loops in $\mathbb{C}\setminus\{0\}$
-- statement:
--   Let $a\le b$ and let $F:[a,b]\times\mathbb{R}\to\mathbb{C}$ be continuous, such that for every $\lambda\in[a,b]$ the loop $F_\lambda=F(\lambda,\cdot)$ is $1$-periodic and never vanishes. If $F_a$ has winding number $k\in\mathbb{Z}$, then $F_\lambda$ has winding number $k$ for every $\lambda\in[a,b]$.
--
--   This is the homotopy invariance of the winding number of loops in $\mathbb{C}\setminus\{0\}$, in the form used to compare windings of a function along circles of different radii or centres.
--
--   **Formalization Note** $F$ is `F : ℝ → ℝ → ℂ`; joint continuity is `ContinuousOn (fun p => F p.1 p.2) (Set.Icc a b ×ˢ Set.univ)`. "Winding number $k$" is `HasLoopWind (F λ) k` (a continuous $1$-periodic nowhere-zero loop with a continuous argument $\theta$, $\theta(1)-\theta(0)=2\pi k$). The case $b<a$ is vacuous.
-- source:
--   Standard (degree theory of loops in $\mathbb{C}^*$); used in U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 2.15

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- Homotopy invariance of the winding number. Let `F : ℝ → ℝ → ℂ` be jointly continuous on
`[a, b] × ℝ`, and for each `λ ∈ [a, b]` let `F λ` be a `1`-periodic loop in `ℂ \ {0}`. If `F a`
has winding number `k`, then every loop `F λ`, `λ ∈ [a, b]`, has winding number `k`. -/
theorem hasLoopWind_of_continuousOn_family {a b : ℝ} (F : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hper : ∀ l ∈ Set.Icc a b, Function.Periodic (F l) 1)
    (h0 : ∀ l ∈ Set.Icc a b, ∀ t, F l t ≠ 0) {k : ℤ} (hk : HasLoopWind (F a) k) :
    ∀ l ∈ Set.Icc a b, HasLoopWind (F l) k := by
  sorry

end FiniteEnergyPlane
