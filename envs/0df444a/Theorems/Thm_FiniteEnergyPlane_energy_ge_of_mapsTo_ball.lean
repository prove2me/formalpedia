-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energy_ge_of_mapsTo_ball
-- name    : FiniteEnergyPlane.energy_ge_of_mapsTo_ball
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T23:24:04.209081+00:00
-- url     : https://prove2.me/theorems/d75e7e7e-9717-4d5a-9462-114f25f97e50
-- title:
--   Monotonicity: pseudoholomorphic maps through the center of a small ball have energy at least $c\,r^2$
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $J$ a smooth almost complex structure on an open set $O\subseteq E$, and $K\subseteq O$ compact. There are $r_0>0$ and $c>0$ with the following property. Let $p\in K$, $0<r\le r_0$, let $U\subseteq\mathbb{C}$ be open and let $u$ be $C^\infty$ and $J$-holomorphic on $U$, with $u(U)\subseteq B_r(p)$, $u:U\to B_r(p)$ proper, and $p\in u(U)$. Then
--   $$\int_U\|Du(z)\|^2\,dz\ \ge\ c\,r^2.$$
--
--   **Formalization Note** $B_r(p)$ is the open ball of the norm of $E$ and $\|Du(z)\|$ is the operator norm of the real derivative $\mathbb{C}\to E$. Properness is: $U\cap u^{-1}(L)$ is compact for every compact $L\subseteq B_r(p)$. Zinger states the lower bound for a compact Riemann surface with boundary whose boundary avoids a metric ball of a $J$-compatible metric, with an explicit constant; here the constant $c$ is unspecified.
-- source:
--   A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 3.12; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, p. 152

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Monotonicity lemma: Zinger, *Notes on J-holomorphic maps*, Proposition 3.12 (local form);
Gromov 1985; quoted in Wendl, p. 152. Let `J` be a smooth almost complex structure on an open set
`O ⊆ E` and `K ⊆ O` compact. There are `r₀ > 0` and `c > 0` such that for every `p ∈ K` and
`0 < r ≤ r₀`, every smooth `J`-holomorphic map `u` on an open set `U ⊆ ℂ` that maps `U` properly
into the ball `B_r(p)` and passes through `p` has Dirichlet energy `∫_U ‖Du‖² ≥ c r²`.
(Zinger: a compact Riemann surface with boundary whose boundary image avoids a metric ball
`B_ρ(x)` of a `J`-compatible metric `g`, energy `E_g`, and the explicit bound
`ord_x u · ρ² / (1 + C(x) ρ)⁴`. Here: an open `U ⊆ ℂ` with a proper map into a norm ball of `E`,
the operator-norm Dirichlet energy, and an unspecified constant `c`.) -/
theorem energy_ge_of_mapsTo_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ U : Set ℂ, IsOpen U → ∀ u : ℂ → E, ContDiffOn ℝ ∞ u U →
        JHolomorphic.IsJHolomorphicOn J U u → Set.MapsTo u U (ball p r) →
        (∀ L : Set E, IsCompact L → L ⊆ ball p r → IsCompact (U ∩ u ⁻¹' L)) → p ∈ u '' U →
        ENNReal.ofReal (c * r ^ 2) ≤ ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) := by
  sorry

end FiniteEnergyPlane
