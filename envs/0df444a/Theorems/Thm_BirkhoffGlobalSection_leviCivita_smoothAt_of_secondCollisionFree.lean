-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_leviCivita_smoothAt_of_secondCollisionFree
-- name    : BirkhoffGlobalSection.leviCivita_smoothAt_of_secondCollisionFree
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:07:38.24022+00:00
-- url     : https://prove2.me/theorems/8e70eedd-a7f2-4df1-9c7d-4efb2672da77
-- title:
--   Smoothness of the Levi-Civita Hamiltonian on its regular domain
-- statement:
--   For every $\mu,c\in\mathbb R$, the totalized Levi-Civita Hamiltonian $K_{\mu,c}$ is ambiently $C^\infty$ at every phase point satisfying $D(z)>0$.
--
--   This is exactly the domain on which the remaining inverse-distance denominator in equation (2.2) is nonsingular. It includes the regularized collision over the chosen primary, where $z=0$ and $D(z)=1$.
-- source:
--   Joung--van Koert, equation (2.2), https://arxiv.org/abs/2407.19159v3. Smoothness away from |2z^2-1| = 0 is an analytic consequence of the displayed formula.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- The Levi-Civita Hamiltonian is smooth away from the unregularized second
collision. -/
theorem leviCivita_smoothAt_of_secondCollisionFree (μ c : ℝ) (s : Phase)
    (hD : 0 < secondCollisionDistanceSq s) :
    ContDiffAt ℝ ∞ (leviCivitaHamiltonian μ c) s := by sorry

end BirkhoffGlobalSection
