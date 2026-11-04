-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_shiftA_comp_affine_of_range_eq
-- name    : FiniteEnergyPlane.exists_shiftA_comp_affine_of_range_eq
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T21:10:40.005149+00:00
-- url     : https://prove2.me/theorems/019c1fdb-a6c0-42c0-8bd1-e02ce1513cbb
-- title:
--   Embedded fast planes with the same image differ by an affine reparametrization and a translation
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate) and let $u$ and $v$ be embedded fast finite-energy planes asymptotic to $P$ at $\infty$ with $\mathrm{proj}(u(\mathbb{C}))=\mathrm{proj}(v(\mathbb{C}))$. Then there are $c\in\mathbb{R}$ and $A,B\in\mathbb{C}$ with $A\neq0$ such that $u(Az+B)=(c\cdot v)(z)$ for all $z\in\mathbb{C}$.
--
--   **Formalization Note** The puncture at $\infty$ is `IsNondegenerateEnd H u cylInf P 1` (nondegenerate in the sense of Hryniewicz 2014, Definition 2.9); "fast" is `IsFastPlane`, "embedded" is `IsEmbeddedPlane`. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$; $P$ itself need not be nondegenerate. Hryniewicz writes the hypothesis as $\mu(\tilde u)\ge3$, where $\mu(\tilde u)$ is the index of $P$ in the class of trivializations of $\xi$ along $P$ that extend over the capping disk $u$. On a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so $\mu(\tilde u)$ is determined by $P$ and equals the index in that frame. The translation $c\cdot v$ is `shiftA c v`, $z\mapsto e^{2c}v(z)$. Hryniewicz's assumption $\beta_{\tilde u}=\beta_{\tilde v}$ holds for any two planes asymptotic to $P$ on a strictly star-shaped level (global frame of $\xi$) and is not restated. Of Hryniewicz's dichotomy (equal or disjoint images), only the case of equal images is stated here.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.25

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 6.25. Let `u` and `v` be embedded fast finite-energy planes
asymptotic to the same orbit `P` at `∞`, where the Conley–Zehnder index of `P` is at least `3`. If
`proj H ∘ u` and `proj H ∘ v` have the same image, then `u` and `v` differ by an affine
reparametrization and a translation in the symplectization: `u(Az + B) = (c · v)(z)` for all `z`,
for some `c ∈ ℝ` and `A, B ∈ ℂ` with `A ≠ 0`. -/
theorem exists_shiftA_comp_affine_of_range_eq (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1) (hve : IsEmbeddedPlane v)
    (hrange : Set.range (proj H ∘ u) = Set.range (proj H ∘ v)) :
    ∃ (c : ℝ) (A B : ℂ), A ≠ 0 ∧ ∀ z, u (A * z + B) = shiftA c v z := by
  sorry

end FiniteEnergyPlane
