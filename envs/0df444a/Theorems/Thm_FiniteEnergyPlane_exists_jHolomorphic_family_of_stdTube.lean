-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_jHolomorphic_family_of_stdTube
-- name    : FiniteEnergyPlane.exists_jHolomorphic_family_of_stdTube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T13:00:27.118887+00:00
-- url     : https://prove2.me/theorems/c301cb05-2117-4c08-bc58-7cd84b023ecd
-- title:
--   From $\bar J$-holomorphic planes in a tube to $\tilde J$-holomorphic planes near a fast plane
-- statement:
--   Let $H$ be a strictly star-shaped level function on $\mathbb{R}^4$, $J$ a compatible complex structure on $\xi$, $\tilde J$ the induced almost complex structure on the symplectization $\mathbb{R}^4 \setminus \{0\}$, and $P = (x, T)$ a periodic Reeb orbit. Let $u$ be a fast finite-energy plane with a nondegenerate end at $P$, and let $\delta < 0$ be such that every eigenvalue of the asymptotic operator $A_P$ below $\delta$ has winding number $\le 1$ and every eigenvalue above $\delta$ has winding number $\ge 2$. Let $l \ge 1$.
--
--   **Tube data.** Let $\rho, b > 0$, let $\Phi : \mathbb{C} \times \mathbb{C} \to \mathbb{R}^4$ be $C^\infty$ and let $\bar J$ be a field of real endomorphisms of $\mathbb{C} \times \mathbb{C}$, such that
--   - $\Phi(z, 0) = u(z)$ for all $z$;
--   - for every $p \in \mathbb{C} \times B_\rho(0)$: $\Phi(p) \ne 0$, $D\Phi(p)$ is injective and $D\Phi(p) \circ \bar J(p) = \tilde J(\Phi(p)) \circ D\Phi(p)$;
--   - $D\Phi(0,0)(\tau, 1) = u(0)$ for some $\tau \in \mathbb{C}$;
--   - there are $d, c \in \mathbb{R}$ and $\alpha$, $X$, smooth on $\mathbb{R} \times B_\rho(0)$ and $1$-periodic in $t$, with $\alpha(t, 0) = 0$, $X(t, 0) = x(Tt + c)$, such that $a(\Phi(e^{2\pi(s+it)}, w)) - Ts - d - \alpha(t, w)$ and $\mathrm{proj}(\Phi(e^{2\pi(s+it)}, w)) - X(t, w)$ decay exponentially at rate $b$ in $C^\infty$ as $s \to \infty$, uniformly in $t$ and $w \in B_\rho(0)$ (`ExpDecayCInftyTube`).
--
--   **Family in the tube.** Let $r > 0$ and let $G : \mathbb{C} \times \mathbb{R} \to \mathbb{C} \times \mathbb{C}$ be $C^l$ on $\mathbb{C} \times (-r, r)$ with $G(z, 0) = (z, 0)$ and $[\partial_t G(0,0)]_2 = i$, such that
--   - for each $t \in (-r, r)$, $G_t = G(\cdot, t) = (\psi_t, v_t)$ is $C^\infty$, takes values in $\mathbb{C} \times B_\rho(0)$, is $\bar J$-holomorphic on $\mathbb{C}$, and for some $C$ and $\beta > 0$ (depending on $t$)
--   $$|\psi_t(z) - z| \le C(1+|z|)^{1-\beta}, \qquad |v_t(z)| \le C(1+|z|)^{\delta/2\pi},$$
--   and for every $z$ there is $\Delta \in \mathbb{C}$ with $[DG(z,t)(\Delta, 1)]_1 = 0$ and $|[DG(z,t)(\Delta, 1)]_2| \le C(1+|z|)^{\delta/2\pi}$;
--   - for every $\varepsilon > 0$ there is $r' \in (0, r]$ such that for $|t| < r'$ and all $z$:
--   $$|\psi_t(z) - z| \le \varepsilon(1+|z|), \quad |v_t(z)| \le \varepsilon, \quad \|D\psi_t(z) - \mathrm{id}\| \le \varepsilon, \quad (1+|z|)\,\|Dv_t(z)\| \le \varepsilon.$$
--
--   **Conclusion.** There are $r > 0$ and $g : \mathbb{C} \times \mathbb{R} \to \mathbb{R}^4$, $C^l$ on $\mathbb{C} \times (-r, r)$, with $g(z, 0) = u(z)$, such that
--   - for each $t \in (-r, r)$: $g(\cdot, t)$ is $C^\infty$, avoids $0$, is $\tilde J$-holomorphic on $\mathbb{C}$ and has a nondegenerate end at $P$; there is $C$ with $\operatorname{dist}\big(\mathrm{proj}\, g(z, t), x(\mathbb{R})\big) \le C(1+|z|)^{\delta/2\pi}$ for all $z$; and there is $C$ such that for every $z$ some $\Delta \in \mathbb{C}$ has $\|Dg(z,t)(\Delta, 1)\| \le C(1+|z|)^{\delta/2\pi}\,\|g(z,t)\|$;
--   - if $Dg(0,0)(\Delta, \delta t) + \lambda\, g(0,0) = 0$ with $\Delta \in \mathbb{C}$, $\delta t, \lambda \in \mathbb{R}$, then $\Delta = 0$, $\delta t = 0$, $\lambda = 0$;
--   - for every $\varepsilon > 0$ there is $r' \in (0, r]$ such that $g(\cdot, t)$ is $\varepsilon$-close to $u$ in the sense of `IsCylCloseTo H ε` for $|t| < r'$.
--
--   **Role.** Transfers a family of holomorphic planes given in tube coordinates $(z, w)$ around a fast plane to a family of $\tilde J$-holomorphic planes in the symplectization, together with its asymptotic, transversality and closeness properties. The hypotheses on $\Phi$ and on $G$ are stated separately from any construction of the tube or of the family, so the statement applies to any tube and any family with these properties.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); asymptotic operators and windings as in H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- From a family of `Jbar`-holomorphic planes in a tube to a family of `J̃`-holomorphic planes.
Let `u` be a fast finite-energy plane with a nondegenerate end at `P`, and `δ < 0` such that every
eigenvalue of `A_P` below `δ` has winding at most `1` and every eigenvalue above `δ` has winding
at least `2`. Let `Φ : ℂ × ℂ → V 1` be smooth with `Φ(z, 0) = u z`, nonvanishing with injective
derivative and `DΦ ∘ Jbar = J̃(Φ) ∘ DΦ` on `ℂ × ball 0 ρ`, with `DΦ(0, 0)(τ, 1) = u 0` for some
`τ`, and with an exponentially attained cylindrical model `(T s + d + α(t, w), X(t, w))` at `∞`.
Let `G : ℂ × (-r, r) → ℂ × ℂ` be a `C^l` family of smooth `Jbar`-holomorphic planes in
`ℂ × ball 0 ρ` with `G(z, 0) = (z, 0)`, normal velocity `i` at `(0, 0)`, tangential part
`z + O((1+‖z‖)^{1-β})`, normal part `O((1+‖z‖)^{δ/2π})` with a `t`-derivative of the same order,
and converging to `(z, 0)` in weighted `C¹` as `t → 0`. Then there are `r > 0` and a `C^l` map
`g : ℂ × (-r, r) → V 1` with `g(·, 0) = u` such that for every `t`: `g(·, t)` is smooth, avoids
`0`, is `J̃`-holomorphic and asymptotic to `P` at `∞`; the distance from `proj (g(z, t))` to the
image of `P` is at most `C (1 + ‖z‖)^{δ/2π}`; and some `Δ` has
`‖Dg(z, t)(Δ, 1)‖ ≤ C (1 + ‖z‖)^{δ/2π} ‖g(z, t)‖`. At `(0, 0)`,
`Dg(0, 0)(Δ, δt) + λ • g(0, 0) = 0` forces `Δ = 0`, `δt = 0`, `λ = 0`, and `g(·, t)` tends to
`u` in the sense of `IsCylCloseTo` as `t → 0`. -/
theorem exists_jHolomorphic_family_of_stdTube (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (l : ℕ) (hl : 1 ≤ l)
    (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) (Φ : ℂ × ℂ → V 1) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦu : ∀ z, Φ (z, 0) = u z)
    (hΦp : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, Φ p ≠ 0 ∧ Function.Injective (fderiv ℝ Φ p) ∧
        (fderiv ℝ Φ p).comp (Jbar p) = (Jtilde H J (Φ p)).comp (fderiv ℝ Φ p))
    (hτ : ∃ τ : ℂ, fderiv ℝ Φ (0, 0) (τ, 1) = u 0)
    (hmodel : ∃ (d c : ℝ) (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
        ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
        (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t + c)) ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          aCoord H (Φ (cylInf q.1 q.2.1, q.2.2)) - P.T * q.1 - d - α (q.2.1, q.2.2)) ρ b ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          proj H (Φ (cylInf q.1 q.2.1, q.2.2)) - X (q.2.1, q.2.2)) ρ b)
    (r : ℝ) (hr : 0 < r) (G : ℂ × ℝ → ℂ × ℂ)
    (hG : ContDiffOn ℝ l G (Set.univ ×ˢ Set.Ioo (-r) r))
    (hG0 : ∀ z, G (z, 0) = (z, 0)) (hGω : (fderiv ℝ G (0, 0) (0, 1)).2 = Complex.I)
    (hGt : ∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => G (z, t)) ∧ (∀ z, (G (z, t)).2 ∈ ball (0 : ℂ) ρ) ∧
        JHolomorphic.IsJHolomorphicOn Jbar Set.univ (fun z => G (z, t)) ∧
        (∃ C β : ℝ, 0 < β ∧ ∀ z, ‖(G (z, t)).1 - z‖ ≤ C * (1 + ‖z‖) ^ (1 - β)) ∧
        (∃ C : ℝ, ∀ z, ‖(G (z, t)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, (fderiv ℝ G (z, t) (Δ, 1)).1 = 0 ∧
          ‖(fderiv ℝ G (z, t) (Δ, 1)).2‖ ≤ C * (1 + ‖z‖) ^ (δ / (2 * π)))
    (hGc : ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r', ∀ z,
        ‖(G (z, t)).1 - z‖ ≤ ε * (1 + ‖z‖) ∧ ‖(G (z, t)).2‖ ≤ ε ∧
        ‖fderiv ℝ (fun z => (G (z, t)).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε ∧
        (1 + ‖z‖) * ‖fderiv ℝ (fun z => (G (z, t)).2) z‖ ≤ ε) :
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
