-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd
-- name    : FiniteEnergyPlane.exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T20:51:38.423175+00:00
-- url     : https://prove2.me/theorems/354d5d0c-b6c1-4864-bd2a-a493c349bf26
-- title:
--   Asymptotic eigenvector of a plane at a nondegenerate puncture at infinity
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with compatible $J$ on $\xi$, and let $u:\mathbb{C}\to\mathbb{R}^4\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic plane (`IsFiniteEnergyCurve H J Set.univ u`) whose puncture $\infty$ is nondegenerate in the sense of Hryniewicz's Definition 2.9, with asymptotic limit a periodic Reeb orbit $P$ (`IsNondegenerateEnd H u cylInf P 1`). Then $u$ has an asymptotic eigenvalue $\mu$ and an asymptotic eigenvector $v$ of the asymptotic operator $A_P$ at $\infty$ (`HasAsymptoticEigenvector H J u cylInf P 1 μ v`), in the cylindrical coordinates $(s,t)\mapsto e^{2\pi(s+it)}$.
--
--   Role: Theorem 2.11 of Hryniewicz (JSG 2014) stated directly at the puncture $\infty$ of a plane, with no assumption on the spectrum of $A_P$.
--
--   **Formalization Note** $P$ need not be nondegenerate as an orbit; only the puncture is assumed nondegenerate (`IsNondegenerateEnd`). The sign of the puncture is $+1$, so `HasAsymptoticEigenvector` includes $\mu<0$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.22 / (100); U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.11

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz, Theorem 2.11 at the puncture `∞` of a plane in `ℝ⁴`: let `u` be a finite-energy
`J̃`-holomorphic plane whose puncture `∞` is nondegenerate (Definition 2.9) with asymptotic limit
`P`, in the cylindrical coordinates `cylInf`. Then `u` has an asymptotic eigenvalue `μ` and an
asymptotic eigenvector `v` of `A_P` at `∞`, in the same coordinates. -/
theorem exists_hasAsymptoticEigenvector_cylInf_of_isNondegenerateEnd (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hfe : IsFiniteEnergyCurve H J Set.univ u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ (μ : ℝ) (v : ℝ → V 1), HasAsymptoticEigenvector H J u cylInf P 1 μ v := by
  sorry

end FiniteEnergyPlane
