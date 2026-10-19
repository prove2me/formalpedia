-- Prove2me | Theorems.Thm_FlatlyFoliated_decaying_drift_eq_zero
-- name    : FlatlyFoliated.decaying_drift_eq_zero
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T17:06:47.385406+00:00
-- url     : https://prove2.me/theorems/f653c6ed-d9a2-429f-b01c-1768013f38b6
-- title:
--   A decaying solution of the FFR drift equation vanishes
-- statement:
--   Let $\eta,u:\mathbb R^3\to\mathbb R$ be smooth functions, with $\eta(x)>0$ everywhere. If
--   $$
--   \eta\,\Delta u=\langle\nabla\eta,\nabla u\rangle,
--   \qquad \lim_{|x|\to\infty}u(x)=0,
--   $$
--   then
--   $$
--   u(x)=0\quad\text{for every }x\in\mathbb R^3.
--   $$
--   This is the maximum-principle implication used after equation (45) in the proof of Theorem 2. Taking $u=\nabla\cdot\zeta$ makes the elliptic FFR system divergence-free and permits recovery of the original FFR equations.
--
--   **Formalization Note** The equation is multiplied by the positive coefficient $\eta$. The limit is along the cobounded filter on Euclidean three-space.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, p.10, proof of Theorem 2, equation (45) and the maximum-principle implication immediately following it. https://arxiv.org/html/1911.00967v2#Thmtheorem2

import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

theorem decaying_drift_eq_zero (η u : R3 → ℝ)
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (hηpos : ∀ x, 0 < η x)
    (heq : ∀ x, η x * lap u x = ∑ i, pd i η x * pd i u x)
    (hinf : Filter.Tendsto u (Bornology.cobounded R3) (nhds 0)) :
    ∀ x, u x = 0 := by sorry

end FlatlyFoliated
