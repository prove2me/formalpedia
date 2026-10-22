-- Prove2me | Theorems.Thm_FiniteEnergyPlane_asympOp_symm
-- name    : FiniteEnergyPlane.asympOp_symm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:41:23.032441+00:00
-- url     : https://prove2.me/theorems/83dae61a-fe0c-417e-8eca-993207c169a1
-- title:
--   The asymptotic operator is symmetric
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $P=(x,T)$ a periodic Reeb orbit, and $\eta,\zeta$ two $\xi$-loops along $P$. Then $A_P\eta$ is a $\xi$-loop along $P$, and
--   $$\int_0^1\omega_0\big(A_P\eta(t),J(x(Tt))\zeta(t)\big)\,dt=\int_0^1\omega_0\big(\eta(t),J(x(Tt))A_P\zeta(t)\big)\,dt.$$
--
--   **Formalization Note** $A_P$ is `asympOp J P`, acting pointwise on functions `ℝ → V n`; the integrals are interval integrals over $[0,1]$.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 2.5 and Remark 2.6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, Definition 2.5: the asymptotic operator `A_P` maps `ξ`-loops to `ξ`-loops and is
symmetric for the `L²` pairing `⟨η, ζ⟩ = ∫₀¹ ω₀(η(t), J(x(Tt)) ζ(t)) dt`. -/
theorem asympOp_symm {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (η ζ : ℝ → V n) (hη : IsXiLoop P η) (hζ : IsXiLoop P ζ) :
    IsXiLoop P (asympOp J P η) ∧
      ∫ t in (0 : ℝ)..1, omega0 (asympOp J P η t) (J (P.x (P.T * t)) (ζ t)) =
        ∫ t in (0 : ℝ)..1, omega0 (η t) (J (P.x (P.T * t)) (asympOp J P ζ t)) := by
  sorry

end FiniteEnergyPlane
