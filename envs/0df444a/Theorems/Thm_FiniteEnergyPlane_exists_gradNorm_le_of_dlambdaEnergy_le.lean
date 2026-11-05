-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_gradNorm_le_of_dlambdaEnergy_le
-- name    : FiniteEnergyPlane.exists_gradNorm_le_of_dlambdaEnergy_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T17:09:28.133461+00:00
-- url     : https://prove2.me/theorems/e2c8fd8f-d0cc-41e0-80b1-d8c7607d7ab9
-- title:
--   Gradient bounds for curves whose $d\lambda$-energy lies below every period
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level. Let $U_k\subset\mathbb{C}$ be open, increasing, with $\bigcup_k U_k=\mathbb{C}\setminus\{0\}$, and let $v_k$ be finite-energy $\tilde J$-holomorphic curves on $U_k$ with Hofer energy at most $C$ and $d\lambda$-energy at most $e$, where $e$ is smaller than the period of every periodic Reeb orbit of period at most $C$. Then on every compact $K\subset\mathbb{C}\setminus\{0\}$ the $\mathbb{R}$-invariant gradient norm of $v_k$ is bounded by a constant $M$ for all large $k$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, Lemma 4.11; H. Hofer, K. Wysocki, E. Zehnder, Finite energy cylinders of small area, Ergodic Theory Dynam. Systems 22 (2002), 1451-1486, Theorem 1.1

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Gradient bounds for curves with small `dλ`-energy. Let `U_k` be open, increasing, with
`⋃ U_k = ℂ \ {0}`, and let `v_k` be finite-energy `J̃`-holomorphic curves on `U_k` with Hofer energy
at most `C` and `dλ`-energy at most `e`, where `e` is smaller than every period at most `C` of a
periodic Reeb orbit. Then for every compact `K ⊆ ℂ \ {0}` the `ℝ`-invariant norm `gradNorm` of `v_k`
is bounded on `K` by a constant `M` for all large `k`. -/
theorem exists_gradNorm_le_of_dlambdaEnergy_le {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (U : ℕ → Set ℂ) (hUo : ∀ k, IsOpen (U k))
    (hUm : Monotone U) (hUu : ⋃ k, U k = {z : ℂ | z ≠ 0}) (v : ℕ → ℂ → V n)
    (hv : ∀ k, IsFiniteEnergyCurve H J (U k) (v k)) (C e : ℝ)
    (hE : ∀ k, energy H (U k) (v k) ≤ ENNReal.ofReal C)
    (hd : ∀ k, dlambdaEnergy H (U k) (v k) ≤ ENNReal.ofReal e)
    (he₁ : ∀ Q : ReebOrbit H, Q.T ≤ C → e < Q.T) (K : Set ℂ) (hK : IsCompact K)
    (hK0 : K ⊆ {z : ℂ | z ≠ 0}) :
    ∃ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K, gradNorm H (v k) z ≤ M := by
  sorry

end FiniteEnergyPlane
