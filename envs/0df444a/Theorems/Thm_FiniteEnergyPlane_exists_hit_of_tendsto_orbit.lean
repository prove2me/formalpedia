-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hit_of_tendsto_orbit
-- name    : FiniteEnergyPlane.exists_hit_of_tendsto_orbit
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:48:39.54604+00:00
-- url     : https://prove2.me/theorems/7cec9d32-680a-49bf-9297-26b798e8e476
-- title:
--   A trajectory accumulating on $P$ meets every fast plane over $P$ at arbitrarily large times
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate unless stated otherwise). Let $u$ be a fast finite-energy plane asymptotic to $P$ at $\infty$, and let $y$ be a Reeb trajectory with $y(0)\notin x(\mathbb{R})$.
--   1. If $y(s_k)$ converges to a point of $x(\mathbb{R})$ for some $s_k\to+\infty$, then for every $n\in\mathbb{R}$ there is $t>n$ with $y(t)\in\mathrm{proj}(u(\mathbb{C}))$.
--   2. If $y(s_k)$ converges to a point of $x(\mathbb{R})$ for some $s_k\to-\infty$, then for every $n\in\mathbb{R}$ there is $t<n$ with $y(t)\in\mathrm{proj}(u(\mathbb{C}))$.
--
--   **Formalization Note** The hypotheses of 1 and 2 say that the $\omega$-limit set, respectively the $\alpha$-limit set, of $y(0)$ meets $x(\mathbb{R})$. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated. The plane $u$ is not assumed to be embedded.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.9; H. Hofer, K. Wysocki, E. Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), 197–289, Section 5

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 6.9; Hofer–Wysocki–Zehnder (Ann. of Math. 1998), § 5. Let `u`
be a fast finite-energy plane asymptotic to `P` at `∞`, where the Conley–Zehnder index of `P` is at
least `3`, and let `y` be a Reeb trajectory with `y 0 ∉ x(ℝ)`. If a point of `x(ℝ)` is a limit of
`y(tₖ)` for some `tₖ → +∞` (that is, the `ω`-limit set of `y 0` meets `x(ℝ)`), then `y` meets
`proj H ∘ u` at times larger than any given `n`. The same holds for `tₖ → -∞` (the `α`-limit set)
and times smaller than any given `n`. -/
theorem exists_hit_of_tendsto_orbit (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (hy₀ : y 0 ∉ Set.range P.x) :
    ((∃ (τ₀ : ℝ) (s : ℕ → ℝ), Tendsto s atTop atTop ∧ Tendsto (y ∘ s) atTop (𝓝 (P.x τ₀))) →
      ∀ n : ℝ, ∃ t > n, y t ∈ Set.range (fun z => proj H (u z))) ∧
    ((∃ (τ₀ : ℝ) (s : ℕ → ℝ), Tendsto s atTop atBot ∧ Tendsto (y ∘ s) atTop (𝓝 (P.x τ₀))) →
      ∀ n : ℝ, ∃ t < n, y t ∈ Set.range (fun z => proj H (u z))) := by
  sorry

end FiniteEnergyPlane
