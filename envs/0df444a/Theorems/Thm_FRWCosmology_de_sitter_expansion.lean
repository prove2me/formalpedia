-- Prove2me | Theorems.Thm_FRWCosmology_de_sitter_expansion
-- name    : FRWCosmology.de_sitter_expansion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:47:20.076908+00:00
-- url     : https://prove2.me/theorems/cb7872f8-3de6-4b7b-9867-fed0dedcd291
-- title:
--   de Sitter universe: $w = -1$ forces $a(t) = a(s)e^{H_0(t-s)}$
-- statement:
--   Let a flat FRW universe ($K = 0$) with $G \neq 0$ carry vacuum energy, i.e. the linear
--   equation of state with $w = -1$, so $p = -\rho$. Then there is a constant $H_0$ such that
--   for all times $s, t$ of the domain
--
--   $$a(t) = a(s)\,e^{H_0 (t - s)} .$$
--
--   The continuity equation forces $\dot\rho = 0$, so the density is constant; the first
--   Friedmann equation then makes $H^2$ constant, and continuity of $H$ on a connected domain
--   makes $H$ itself constant, equal to $H_0$. Integrating $\dot a / a = H_0$ gives the
--   exponential expansion characteristic of the de Sitter universe.
-- source:
--   Konstantinos Xenos, An Introduction to FRW Cosmology and dark energy models, University of Patras undergraduate thesis, 2020, arXiv:2101.06135v1, https://arxiv.org/abs/2101.06135, pp. 64-65, §4.4, the case $w = -1$ (eq. (4.39) and the display after it)

import Definitions.Def_FRWUniverse

namespace FRWCosmology

theorem de_sitter_expansion (U : FRWUniverse) (hG : U.G ≠ 0) (hK : U.K = 0)
    (hw : U.LinearEoS (-1)) :
    ∃ H₀ : ℝ, ∀ s ∈ U.I, ∀ t ∈ U.I, U.a t = U.a s * Real.exp (H₀ * (t - s)) := by sorry

end FRWCosmology
