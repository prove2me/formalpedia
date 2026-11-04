-- Prove2me | Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
-- name    : FiniteEnergyPlane.proj_not_mem_range_of_isFastPlane
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T21:10:21.683016+00:00
-- url     : https://prove2.me/theorems/70c253bd-8253-4907-a639-968088768d38
-- title:
--   Embedded fast planes of index at least three miss the cylinder over their asymptotic orbit
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P=(x,T)$ be a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate) and $u$ an embedded fast finite-energy plane asymptotic to $P$ at $\infty$. Then $u(\mathbb{C})$ does not meet the cylinder $\mathbb{R}\times x(\mathbb{R})$.
--
--   **Formalization Note** The puncture at $\infty$ is `IsNondegenerateEnd H u cylInf P 1` (nondegenerate in the sense of Hryniewicz 2014, Definition 2.9); "fast" is `IsFastPlane`, "embedded" is `IsEmbeddedPlane`. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$; $P$ itself need not be nondegenerate. Hryniewicz writes the hypothesis as $\mu(\tilde u)\ge3$, where $\mu(\tilde u)$ is the index of $P$ in the class of trivializations of $\xi$ along $P$ that extend over the capping disk $u$. On a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so $\mu(\tilde u)$ is determined by $P$ and equals the index in that frame. The conclusion is $\mathrm{proj}(u(z))\notin x(\mathbb{R})$ for every $z$, the cylinder being the cone $\{y\neq0:\mathrm{proj}(y)\in x(\mathbb{R})\}$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.24; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations III: Fredholm theory, in Topics in Nonlinear Analysis, Progr. Nonlinear Differential Equations Appl. 35, Birkhäuser 1999, 381–475, doi:10.1007/978-3-0348-8765-6_18, Lemma 8.1

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 6.24. Let `u` be an embedded fast finite-energy plane
asymptotic to `P` at `∞`, where the Conley–Zehnder index of `P` is at least `3`. Then `u` does not
meet the cone `ℝ × x(ℝ)`: `proj H (u z) ∉ x(ℝ)` for every `z`. -/
theorem proj_not_mem_range_of_isFastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∀ z, proj H (u z) ∉ Set.range P.x := by
  sorry

end FiniteEnergyPlane
