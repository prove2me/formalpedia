-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_re_conj_mul_pos
-- name    : FiniteEnergyPlane.hasLoopWind_of_re_conj_mul_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T10:06:20.978423+00:00
-- url     : https://prove2.me/theorems/cee86d91-e882-4f6a-bb1f-3895202af7ca
-- title:
--   A loop in the half-plane on the side of a reference loop has the same winding number
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be a continuous $1$-periodic loop with winding number $k\in\mathbb{Z}$, and let $f:\mathbb{R}\to\mathbb{C}$ be continuous and $1$-periodic with
--   $$\operatorname{Re}\big(\overline{g(t)}\,f(t)\big)>0\qquad\text{for all }t,$$
--   i.e. $f(t)$ lies in the open half-plane bounded by the line through $0$ orthogonal to $g(t)$, on the side of $g(t)$. Then $f$ never vanishes and has winding number $k$.
--
--   This is a comparison principle for winding numbers. In particular it applies when $|f(t)-g(t)|<|g(t)|$ for all $t$, and it is insensitive to multiplying $f$ by a positive function. It is used to identify the asymptotic winding of a curve end with the winding of a limiting loop.
--
--   **Formalization Note** "Winding number $k$" is `HasLoopWind f k` (continuous, $1$-periodic, nowhere zero, with a continuous argument $\theta$ satisfying $\theta(1)-\theta(0)=2\pi k$); $\overline{g(t)}$ is `starRingEnd ℂ (g t)`.
-- source:
--   Standard comparison principle for winding numbers (dog-on-a-leash lemma); used in U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 2.16

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- Let `g` be a loop in `ℂ \ {0}` with winding number `k`, and `f` a continuous `1`-periodic loop
with `Re(conj (g t) · f t) > 0` for all `t` (so `f(t)` lies in the open half-plane on the side of
`g(t)`). Then `f` also has winding number `k`. -/
theorem hasLoopWind_of_re_conj_mul_pos {f g : ℝ → ℂ} {k : ℤ} (hg : HasLoopWind g k)
    (hf : Continuous f) (hper : Function.Periodic f 1)
    (hpos : ∀ t, 0 < (starRingEnd ℂ (g t) * f t).re) : HasLoopWind f k := by
  sorry

end FiniteEnergyPlane
