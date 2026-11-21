-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_forall_norm_lt_of_eq_shiftA_self
-- name    : FiniteEnergyPlane.exists_forall_norm_lt_of_eq_shiftA_self
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T00:13:44.647394+00:00
-- url     : https://prove2.me/theorems/f0d9310b-e842-4377-8a34-d1b3f9c8d0e1
-- title:
--   Coincidences of a fast plane with its bounded nontrivial translates stay in a compact set
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde u:\mathbb{C}\to\mathbb{R}^4$ a fast finite-energy plane asymptotic to the periodic Reeb orbit $P$ at $\infty$. For $\tau\in\mathbb{R}$ write $\tau\cdot\tilde u=e^{2\tau}\tilde u$ for the translate of $\tilde u$ by $\tau$ in the $\mathbb{R}$-direction of the symplectization. Then for every $C$ there is $R$ such that
--   $$\tilde u(z)=(\tau\cdot\tilde u)(w),\quad \tau\neq0,\quad |\tau|\le C\ \Longrightarrow\ |z|<R\text{ and }|w|<R .$$
--
--   Role: coincidences of a fast plane with its own translates by a bounded nonzero amount stay in a compact part of the domain. This is the compactness input for arguments that vary the translation parameter.
--
--   **Formalization Note** $\tau\cdot\tilde u$ is `shiftA τ u`. "Fast" is `IsFastPlane`; the end at $\infty$ is `IsNondegenerateEnd H u cylInf P 1`. Neither embeddedness nor any index condition on $P$ is assumed.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.24 and (100)

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Coincidences of a fast plane with its bounded nontrivial translates stay in a compact set.
Let `u` be a fast finite-energy plane asymptotic to `P` at `∞`. For every `C` there is `R` such
that whenever `u z = (τ · u) w` with `τ ≠ 0` and `|τ| ≤ C`, both `‖z‖ < R` and `‖w‖ < R`. -/
theorem exists_forall_norm_lt_of_eq_shiftA_self (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∀ C : ℝ, ∃ R : ℝ, ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ u w → τ ≠ 0 → |τ| ≤ C →
      ‖z‖ < R ∧ ‖w‖ < R := by
  sorry

end FiniteEnergyPlane
