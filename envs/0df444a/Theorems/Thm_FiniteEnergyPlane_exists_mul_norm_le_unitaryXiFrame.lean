-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_le_unitaryXiFrame
-- name    : FiniteEnergyPlane.exists_mul_norm_le_unitaryXiFrame
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T15:38:55.594461+00:00
-- url     : https://prove2.me/theorems/fe6eb0aa-7746-4bd8-ae62-c04862c3de01
-- title:
--   A unitary frame of the contact structure along a periodic Reeb orbit is uniformly injective
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$, let $J$ be a complex structure on $\xi$, let $P = (x, T)$ be a periodic Reeb orbit, and let $Z(t) : \mathbb{R}^2 \to \mathbb{R}^4$ be a unitary frame of $\xi$ along $P$: smooth, $1$-periodic, onto $\xi_{x(Tt)}$, with $J Z = Z J_0$ and $\omega_0(Z a, Z b) = \langle J_0 a, b\rangle$. Then there is $c > 0$ with $c\,|a| \le |Z(t) a|$ for all $t \in \mathbb{R}$ and $a \in \mathbb{R}^2$.
--
--   Role: inverses of the frame maps $Z(t)$ on $\xi_{x(Tt)}$ are bounded uniformly in $t$, so frame coordinates of $\xi$-vectors are controlled by their norms.
--
--   Formalization Note: $\mathbb{R}^2$ = `CauchyRiemannIndex.Vec 1` with its Euclidean norm; $\mathbb{R}^4$ = `V 1` carries the sup norm.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6.2 (proof of Lemma 6.9)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A unitary frame of `ξ` along a periodic Reeb orbit is uniformly injective: there is `c > 0`
with `c ‖a‖ ≤ ‖Z t a‖` for all `t` and `a`. -/
theorem exists_mul_norm_le_unitaryXiFrame {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1}
    {P : ReebOrbit H} {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1}
    (hZ : IsUnitaryXiFrame J P Z) : ∃ c > 0, ∀ t a, c * ‖a‖ ≤ ‖Z t a‖ := by
  sorry

end FiniteEnergyPlane
