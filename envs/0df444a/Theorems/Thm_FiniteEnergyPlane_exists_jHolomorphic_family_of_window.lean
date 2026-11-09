-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_jHolomorphic_family_of_window
-- name    : FiniteEnergyPlane.exists_jHolomorphic_family_of_window
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-08T22:42:14.186007+00:00
-- url     : https://prove2.me/theorems/bc0a29de-495f-4574-a868-98bd6bc0bce6
-- title:
--   A family of holomorphic maps through an embedded fast plane, for a given decay rate
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^4$ be strictly star-shaped, $J$ a compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on the symplectization $\mathbb R\times S\cong\mathbb R^4\setminus\{0\}$. Let $P$ be a periodic Reeb orbit with $\mu_{CZ}(P)\ge 3$ and let $u:\mathbb C\to\mathbb R^4\setminus\{0\}$ be an embedded fast finite-energy plane asymptotic to $P$ at $\infty$. Let $\delta<0$ be a number that is not an eigenvalue of the asymptotic operator $A_P$, such that every eigenvalue of $A_P$ below $\delta$ has winding number at most $1$ and every eigenvalue above $\delta$ has winding number at least $2$.
--
--   Then for every $l\ge 1$ there are $r>0$ and a map $g:\mathbb C\times\mathbb R\to\mathbb R^4$, of class $C^l$ on $\mathbb C\times(-r,r)$, with $g(\cdot,0)=u$, such that for every $t\in(-r,r)$:
--   - $g(\cdot,t)$ is smooth, avoids $0$, is $\tilde J$-holomorphic and asymptotic to $P$ at $\infty$;
--   - there is $C$ with $\operatorname{dist}(\operatorname{proj}g(z,t),P(\mathbb R))\le C(1+|z|)^{\delta/2\pi}$ for all $z$;
--   - there is $C$ such that for every $z$ some $\Delta\in\mathbb C$ satisfies $\|Dg(z,t)(\Delta,1)\|\le C(1+|z|)^{\delta/2\pi}\|g(z,t)\|$.
--
--   Moreover $Dg(0,0)(\Delta,\delta t)+\lambda\,g(0,0)=0$ implies $\Delta=0$, $\delta t=0$, $\lambda=0$, and for every $\varepsilon>0$ there is $r'\in(0,r]$ such that $g(\cdot,t)$ is $\varepsilon$-close to $u$ in the sense of `IsCylCloseTo` for all $|t|<r'$.
--
--   The statement produces a one-parameter family of holomorphic maps through a fast plane, transverse to the translation direction at one point, with controlled decay at the puncture; it is the existence part of the local structure of the space of fast planes near $u$.
--
--   Formalization Note: the plane is a map `u : ℂ → V 1` with `V 1 = ℝ⁴`; `proj H` is the radial projection to $S$; `IsNondegenerateEnd H u cylInf P 1` is asymptotic convergence to $P$ at $\infty$ with sign $+1$; `HasEigenWind J P μ k` says $\mu$ is an eigenvalue of $A_P$ all of whose eigenvectors have winding $k$; `fderiv ℝ g (z, t) (Δ, 1)` is $D_zg\,\Delta+\partial_tg$.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6 (Lemma 6.10)

import Definitions.Def_FiniteEnergyPlane_CylClose

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A family of `J̃`-holomorphic maps through an embedded fast plane, for a given rate `δ`. Let `u`
be an embedded fast finite-energy plane asymptotic to `P` at `∞`, where the Conley–Zehnder index of
`P` is at least `3`, and let `δ < 0` be a number that is not an eigenvalue of `A_P`, such that every
eigenvalue of `A_P` below `δ` has winding number at most `1` and every eigenvalue above `δ` has
winding number at least `2`. Then for every `l ≥ 1` there are `r > 0` and a `C^l` map
`g : ℂ × (-r, r) → V 1` with `g(·, 0) = u` such that for every `t`: `g(·, t)` is smooth, avoids
`0`, is `J̃`-holomorphic and asymptotic to `P` at `∞`; the distance from `proj (g(z, t))` to the
image of `P` is at most `C (1 + ‖z‖)^{δ/2π}`; and some `Δ` has
`‖Dg(z, t)(Δ, 1)‖ ≤ C (1 + ‖z‖)^{δ/2π} ‖g(z, t)‖`. At `(z, t) = (0, 0)`,
`Dg(0, 0)(Δ, δt) + λ • g(0, 0) = 0` forces `Δ = 0`, `δt = 0`, `λ = 0`. Moreover `g(·, t)` tends
to `u` in the sense of `IsCylCloseTo` as `t → 0`. -/
theorem exists_jHolomorphic_family_of_window (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (δ : ℝ) (hδ : δ < 0) (hδe : ∀ v, ¬ IsAsymptoticEigen J P δ v)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
        JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
        (∃ C : ℝ, ∀ z, infDist (proj H (g (z, t))) (Set.range P.x) ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, ‖fderiv ℝ g (z, t) (Δ, 1)‖ ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π)) * ‖g (z, t)‖) ∧
      (∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, 0) (Δ, δt) + lam • g (0, 0) = 0 →
        Δ = 0 ∧ δt = 0 ∧ lam = 0) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
        IsCylCloseTo H ε (fun z => g (z, t)) u := by
  sorry

end FiniteEnergyPlane
