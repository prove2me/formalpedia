-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFastPlane_of_infDist_le
-- name    : FiniteEnergyPlane.isFastPlane_of_infDist_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T15:14:56.207641+00:00
-- url     : https://prove2.me/theorems/7df78d73-336b-439d-9df6-4c8751f9a291
-- title:
--   A close J-holomorphic plane approaching the orbit at a window rate is fast
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on the contact planes, and let $P$ be a periodic Reeb orbit. Let $u$ be a fast finite-energy plane asymptotic to $P$ at $\infty$, and let $\delta < 0$ be such that every eigenvalue of the asymptotic operator $A_P$ below $\delta$ has winding number at most $1$ and every eigenvalue above $\delta$ has winding number at least $2$, in the global frame of $\xi$.
--
--   Let $f : \mathbb{C} \to V_1$ be smooth, avoid $0$, be $\tilde J$-holomorphic and asymptotic to $P$ at $\infty$ (`IsNondegenerateEnd`), and be $\varepsilon$-close to $u$ in the sense of `IsCylCloseTo` for some $\varepsilon$. If $\operatorname{dist}(\operatorname{proj} f(z), P(\mathbb{R})) \le C (1 + |z|)^{\delta / 2\pi}$ for all $z$, then $f$ is a fast finite-energy plane (`IsFastPlane`).
--
--   **Role.** It identifies the members of a family of $\tilde J$-holomorphic maps near a fast plane as fast planes, as in Hryniewicz (Trans. AMS 2012), Lemma 6.18. In particular, finiteness of the energy of $f$ is part of the conclusion.
--
--   **Formalization Note.** The symplectization $\mathbb{R} \times S$ is $V_1 \setminus \{0\}$, with $y = e^{2a} x$, $a$ = `aCoord H y` and $x$ = `proj H y`. Winding numbers are `HasEigenWind`; $(1 + |z|)^{\delta/2\pi}$ is the cylindrical weight $e^{\delta s}$ for $|z| = e^{2\pi s}$. $P$ may be degenerate, and $\varepsilon$ need not be small.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemma 6.10 and Lemma 6.20

import Definitions.Def_FiniteEnergyPlane_CylClose

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A `J̃`-holomorphic plane close to a fast plane that approaches the orbit at a window rate is
fast. Let `u` be a fast finite-energy plane asymptotic to `P` at `∞`, and let `δ < 0` be such that
every eigenvalue of `A_P` below `δ` has winding number at most `1` and every eigenvalue above `δ`
has winding number at least `2`. Let `f : ℂ → V 1` be smooth, avoid `0`, be `J̃`-holomorphic and
asymptotic to `P` at `∞`, be `ε`-close to `u` in the sense of `IsCylCloseTo` for some `ε`, and have
distance from `proj (f z)` to the image of `P` at most `C (1 + ‖z‖)^{δ/2π}`. Then `f` is a fast
finite-energy plane. -/
theorem isFastPlane_of_infDist_le (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (ε : ℝ) (f : ℂ → V 1) (hf : ContDiff ℝ ∞ f) (hf0 : ∀ z, f z ≠ 0)
    (hfJ : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ f)
    (hfP : IsNondegenerateEnd H f cylInf P 1) (hclose : IsCylCloseTo H ε f u)
    (C : ℝ) (hrate : ∀ z, infDist (proj H (f z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (δ / (2 * π))) :
    IsFastPlane H J f := by
  sorry

end FiniteEnergyPlane
