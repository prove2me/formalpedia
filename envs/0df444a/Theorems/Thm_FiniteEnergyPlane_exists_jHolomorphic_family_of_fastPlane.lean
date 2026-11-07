-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_jHolomorphic_family_of_fastPlane
-- name    : FiniteEnergyPlane.exists_jHolomorphic_family_of_fastPlane
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-06T15:14:58.368524+00:00
-- url     : https://prove2.me/theorems/73020a17-51f1-4611-bd49-9de23ec4c710
-- title:
--   A family of J-holomorphic maps through an embedded fast plane
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on the contact planes, and let $P$ be a periodic Reeb orbit. Assume the Conley–Zehnder index of $P$ is at least $3$ (`P.IsCZAtLeast 3`; $P$ may be degenerate), and let $u$ be an embedded fast finite-energy plane asymptotic to $P$ at $\infty$.
--
--   Then there is $\delta < 0$ such that every eigenvalue of the asymptotic operator $A_P$ below $\delta$ has winding number at most $1$ and every eigenvalue above $\delta$ has winding number at least $2$, in the global frame of $\xi$, and for every integer $l \ge 1$ there are $r > 0$ and a $C^l$ map $g : \mathbb{C} \times (-r, r) \to V_1$ with $g(\cdot, 0) = u$ such that:
--
--   1. for every $t \in (-r, r)$, the map $g(\cdot, t)$ is smooth, avoids $0$, is $\tilde J$-holomorphic and asymptotic to $P$ at $\infty$ (`IsNondegenerateEnd`), and $\partial_t g(\cdot, t)$ is smooth;
--   2. for every $t$ there is $C$ with $\operatorname{dist}(\operatorname{proj} g(z, t), P(\mathbb{R})) \le C (1 + |z|)^{\delta / 2\pi}$ for all $z$;
--   3. for every $t$ there is $C$ such that for every $z$ some $\Delta \in \mathbb{C}$ has $|Dg(z, t)(\Delta, 1)| \le C (1 + |z|)^{\delta/2\pi} |g(z, t)|$;
--   4. for every $t$, the identity $Dg(0, t)(\Delta, \delta t) + \lambda\, g(0, t) = 0$ forces $\Delta = 0$, $\delta t = 0$ and $\lambda = 0$;
--   5. for every $\varepsilon > 0$ there is $r' \in (0, r]$ such that $g(\cdot, t)$ is $\varepsilon$-close to $u$ in the sense of `IsCylCloseTo` for all $|t| < r'$.
--
--   **Role.** This is the existence part of the family of fast planes through $u$ in Hryniewicz (Trans. AMS 2012), Lemma 6.10.
--
--   **Formalization Note.** The symplectization $\mathbb{R} \times S$ is $V_1 \setminus \{0\}$, with $y = e^{2a} x$, $a$ = `aCoord H y` and $x$ = `proj H y`. Winding numbers are `HasEigenWind`; $(1 + |z|)^{\delta/2\pi}$ is the cylindrical weight $e^{\delta s}$ for $|z| = e^{2\pi s}$. Clause 3 measures the $t$-derivative modulo the tangent plane of the member, relative to $|g|$, which is the $\mathbb{R}$-invariant size in the symplectization. Clause 2 compares with the image of $P$, not with a parametrization.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemma 6.10 and Lemma 6.20

import Definitions.Def_FiniteEnergyPlane_CylClose

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A family of `J̃`-holomorphic maps through an embedded fast plane. Let `u` be an embedded fast
finite-energy plane asymptotic to `P` at `∞`, where the Conley–Zehnder index of `P` is at least `3`.
Then there is `δ < 0` such that every eigenvalue of `A_P` below `δ` has winding number at most `1`
and every eigenvalue above `δ` has winding number at least `2`, and for every `l ≥ 1` there are
`r > 0` and a `C^l` map `g : ℂ × (-r, r) → V 1` with `g(·, 0) = u` such that for every `t`: `g(·, t)`
is smooth, avoids `0`, is `J̃`-holomorphic and asymptotic to `P` at `∞`; `∂ₜg(·, t)` is smooth; the
distance from `proj (g(z, t))` to the image of `P` is at most `C (1 + ‖z‖)^{δ/2π}`; some `Δ` has
`‖Dg(z, t)(Δ, 1)‖ ≤ C (1 + ‖z‖)^{δ/2π} ‖g(z, t)‖`; and at `z = 0`,
`Dg(0, t)(Δ, δt) + λ • g(0, t) = 0` forces `Δ = 0`, `δt = 0`, `λ = 0`. Moreover `g(·, t)` tends to
`u` in the sense of `IsCylCloseTo` as `t → 0`. -/
theorem exists_jHolomorphic_family_of_fastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ δ < 0, (∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k)) ∧
      ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
        (∀ z, g (z, 0) = u z) ∧
        (∀ t ∈ Set.Ioo (-r) r,
          ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
          JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t)) ∧
          ContDiff ℝ ∞ (fun z => fderiv ℝ g (z, t) (0, 1)) ∧
          IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
          (∃ C : ℝ, ∀ z, infDist (proj H (g (z, t))) (Set.range P.x) ≤
            C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
          (∃ C : ℝ, ∀ z, ∃ Δ : ℂ, ‖fderiv ℝ g (z, t) (Δ, 1)‖ ≤
            C * (1 + ‖z‖) ^ (δ / (2 * π)) * ‖g (z, t)‖) ∧
          ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, t) (Δ, δt) + lam • g (0, t) = 0 →
            Δ = 0 ∧ δt = 0 ∧ lam = 0) ∧
        ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
          IsCylCloseTo H ε (fun z => g (z, t)) u := by
  sorry

end FiniteEnergyPlane
