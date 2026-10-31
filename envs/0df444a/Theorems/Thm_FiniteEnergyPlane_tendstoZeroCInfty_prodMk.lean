-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_prodMk
-- name    : FiniteEnergyPlane.tendstoZeroCInfty_prodMk
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T11:03:26.831586+00:00
-- url     : https://prove2.me/theorems/92b2520b-8803-43b9-9325-8f1a0d0c0010
-- title:
--   Convergence to zero in C^∞ on a cylindrical end for pairs
-- statement:
--   Let $F,G$ be real normed spaces and $f:\mathbb{R}^2\to F$, $g:\mathbb{R}^2\to G$. If $f\to0$ and $g\to0$ in $C^\infty$ as $s\to+\infty$, uniformly in $t$, then so does the pair $(f,g):\mathbb{R}^2\to F\times G$.
--
--   It lets several quantities on a cylindrical end that converge in $C^\infty$ be bundled into one vector-valued function.
--
--   **Formalization Note** `TendstoZeroCInfty f` means: $f$ is $C^\infty$ on some half-plane $(s_0,\infty)\times\mathbb{R}$, and for every $m$ the $m$-th Fréchet derivative $D^mf(s,t)$ tends to $0$ uniformly in $t$ as $s\to+\infty$.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.10; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

/-- If `f → 0` and `g → 0` in `C^∞` on the end, then so does the pair `(f, g)`. -/
theorem tendstoZeroCInfty_prodMk {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ × ℝ → F} {g : ℝ × ℝ → G}
    (hf : TendstoZeroCInfty f) (hg : TendstoZeroCInfty g) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => (f p, g p)) := by
  sorry

end FiniteEnergyPlane
