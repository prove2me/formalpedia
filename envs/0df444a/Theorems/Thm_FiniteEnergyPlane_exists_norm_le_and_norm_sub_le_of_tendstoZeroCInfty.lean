-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_le_and_norm_sub_le_of_tendstoZeroCInfty
-- name    : FiniteEnergyPlane.exists_norm_le_and_norm_sub_le_of_tendstoZeroCInfty
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T21:09:52.721536+00:00
-- url     : https://prove2.me/theorems/a6b2b351-daa3-48f9-810d-5d3ca36721b1
-- title:
--   Functions decaying in C-infinity on a half-cylinder are eventually small and Lipschitz-small
-- statement:
--   Let $F$ be a real normed space and $f:\mathbb{R}\times\mathbb{R}\to F$ with $f\to0$ in $C^\infty$ on the end (`TendstoZeroCInfty f`: $f$ is smooth on some $(s_0,\infty)\times\mathbb{R}$ and every derivative $D^mf(s,t)$ tends to $0$ uniformly in $t$ as $s\to+\infty$). Then for every $\eta>0$ there is $S$ such that for all $p,q\in\mathbb{R}^2$ with $p_1,q_1\ge S$,
--   $$\|f(p)\|\le\eta\quad\text{and}\quad\|f(p)-f(q)\|\le\eta\,\|p-q\|.$$
--
--   Role: uniform $C^0$ and Lipschitz smallness of $C^\infty$-decaying remainders on a half-cylinder, as used in asymptotic formulas at punctures.
--
--   **Formalization Note** $\|p-q\|$ is the max norm on $\mathbb{R}\times\mathbb{R}$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.22 / (100)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A function on the half-cylinder that tends to `0` in `C^∞` is eventually small and has small
Lipschitz constant: for every `η > 0` there is `S` such that `‖f p‖ ≤ η` and
`‖f p - f q‖ ≤ η ‖p - q‖` for all `p, q` with `p.1, q.1 ≥ S`. -/
theorem exists_norm_le_and_norm_sub_le_of_tendstoZeroCInfty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    (hf : TendstoZeroCInfty f) (η : ℝ) (hη : 0 < η) :
    ∃ S : ℝ, ∀ p q : ℝ × ℝ, S ≤ p.1 → S ≤ q.1 → ‖f p‖ ≤ η ∧ ‖f p - f q‖ ≤ η * ‖p - q‖ := by
  sorry

end FiniteEnergyPlane
