-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_symmetric_half_loop_polar_winding
-- name    : BirkhoffGlobalSection.symmetric_half_loop_polar_winding
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T23:11:39.22712+00:00
-- url     : https://prove2.me/theorems/1d6a8261-6711-4e40-a49a-2835e16425b0
-- title:
--   A reflection-symmetric half-loop winds once
-- statement:
--   A symmetric half-loop in the lower half-plane closes up to a curve winding once around the origin.
--
--   Let $\gamma:\mathbb R\to\mathbb R^2$ be continuous and let $\tau>0$. Assume:
--
--   1. $\gamma(t+2\tau)=\gamma(t)$ for all $t$;
--   2. $\gamma(-t)=\overline{\gamma(t)}$, i.e. $(\gamma_1,\gamma_2)(-t)=(\gamma_1(t),-\gamma_2(t))$;
--   3. $\gamma_2(t)<0$ for $0<t<\tau$;
--   4. $\gamma(0)$ lies on the negative and $\gamma(\tau)$ on the positive horizontal axis.
--
--   Then $\gamma$ never vanishes and has winding number $+1$ over a period. That is, there are continuous $r>0$ and $\theta$ with $\gamma(t)=r(t)(\cos\theta(t),\sin\theta(t))$, $r(t+2\tau)=r(t)$ and
--   $$
--   \theta(t+2\tau)=\theta(t)+2\pi .
--   $$
--
--   This is the topological step turning a $q_2$-symmetric half-orbit into a retrograde loop encircling the primary once in the positive direction. Here the half-orbit starts on the far side of the primary and runs through the lower half-plane to the near side.
--
--   **Formalization Note** The conclusion is the platform predicate `HasPolarWinding γ (2 * τ) 1`.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 1.3 and Section 5 (a retrograde orbit is a simple closed curve encircling the primary once); elementary planar topology.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem symmetric_half_loop_polar_winding (γ : ℝ → Plane) (τ : ℝ) (hτ : 0 < τ)
    (hcont : Continuous γ)
    (hper : ∀ t : ℝ, γ (t + 2 * τ) = γ t)
    (hrefl : ∀ t : ℝ, γ (-t) = ![γ t 0, -γ t 1])
    (hlow : ∀ t ∈ Set.Ioo 0 τ, γ t 1 < 0)
    (hstart : γ 0 1 = 0 ∧ γ 0 0 < 0)
    (hend : γ τ 1 = 0 ∧ 0 < γ τ 0) :
    HasPolarWinding γ (2 * τ) 1 := by sorry

end BirkhoffGlobalSection
