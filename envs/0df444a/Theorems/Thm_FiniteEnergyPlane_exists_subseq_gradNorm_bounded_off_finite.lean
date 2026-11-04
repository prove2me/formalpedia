-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_gradNorm_bounded_off_finite
-- name    : FiniteEnergyPlane.exists_subseq_gradNorm_bounded_off_finite
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T16:24:11.107201+00:00
-- url     : https://prove2.me/theorems/d439d99d-239c-48bf-85a1-554310f7e1a7
-- title:
--   Gradient blow-up of sequences of fast planes happens at finitely many points of the unit disk
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit, $K\subset\mathbb{R}^4$, and $\gamma>0$ smaller than every period at most $T_P$ of a periodic Reeb orbit. Every sequence $(u_k)$ in $\Theta(K,P)$ has a subsequence $(u_{k_j})$ for which there is a finite set $\Gamma$ in the closed unit disk with $\#\Gamma\cdot\gamma\le T_P$ such that
--   1. $|du_{k_j}|$ is uniformly bounded on every compact subset of $\mathbb{C}\setminus\Gamma$;
--   2. every $z\in\Gamma$ is a limit of points $\zeta_j\to z$ with $|du_{k_j}(\zeta_j)|\to\infty$.
--
--   **Formalization Note** $\Theta(K,P)$ is `fastPlaneSet H J P K γ`; $|du|$ is `gradNorm H u`, the sum of the norms of the derivatives of the coordinates $a$ and $\mathrm{proj}\circ u$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Corollaries 4.8, 4.9 and 4.10

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Corollaries 4.8–4.10. Let `P` be a periodic Reeb orbit on
`S ⊂ ℝ⁴` and `0 < γ` smaller than every period at most `P.T`. Every sequence in
`fastPlaneSet H J P K γ` has a subsequence and a finite set `Γ` of points of the closed unit disk,
with `#Γ · γ ≤ P.T`, such that the gradients `gradNorm H uₖ` are uniformly bounded on every compact
subset of `ℂ \ Γ` and every point of `Γ` is a limit of points where the gradients tend to `∞`. -/
theorem exists_subseq_gradNorm_bounded_off_finite (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (K : Set (V 1)) (γ : ℝ) (hγ : 0 < γ)
    (hγ₁ : ∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T)
    (u : ℕ → ℂ → V 1) (hu : ∀ k, u k ∈ fastPlaneSet H J P K γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Γ : Finset ℂ, (∀ z ∈ Γ, ‖z‖ ≤ 1) ∧ (Γ.card : ℝ) * γ ≤ P.T ∧
      (∀ Kc : Set ℂ, Kc ⊆ (↑Γ)ᶜ → IsCompact Kc →
        ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, gradNorm H (u (φ k)) z ≤ M) ∧
      ∀ z ∈ Γ, ∃ ζ : ℕ → ℂ, Tendsto ζ atTop (𝓝 z) ∧
        Tendsto (fun k => gradNorm H (u (φ k)) (ζ k)) atTop atTop := by
  sorry

end FiniteEnergyPlane
