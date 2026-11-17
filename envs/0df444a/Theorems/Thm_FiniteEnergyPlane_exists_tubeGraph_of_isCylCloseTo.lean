-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tubeGraph_of_isCylCloseTo
-- name    : FiniteEnergyPlane.exists_tubeGraph_of_isCylCloseTo
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-16T20:14:15.285347+00:00
-- url     : https://prove2.me/theorems/9fff83ec-1e51-4881-964c-a1fd678e7da2
-- title:
--   A common holomorphic tube for fast planes near an embedded fast plane
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on the contact planes $\xi$, let $\tilde J$ be the induced almost complex structure on $\mathbb{R}^4 \setminus \{0\}$, and let $P$ be a periodic Reeb orbit whose Conley–Zehnder index is at least $3$ (`P.IsCZAtLeast 3`; $P$ may be degenerate). Let $u$ be an embedded fast finite-energy plane asymptotic to $P$ at $\infty$.
--
--   Then there are $\rho > 0$, $b > 0$, $\delta < 0$, $\varepsilon > 0$, a map $\Phi : \mathbb{C} \times \mathbb{C} \to \mathbb{R}^4$ and a standard tube structure $(\bar J, J_\infty, S_\infty)$ of width $\rho$ and rate $b$ (`IsStdTubeStructure ρ b Jbar Jinf Sinf`) such that:
--
--   1. $\Phi$ is injective on $\mathbb{C} \times B_\rho(0)$;
--   2. every eigenfunction of the loop operator $-J_0 \frac{d}{dt} - S_\infty$ with eigenvalue $\mu \le \delta$ has winding at most $0$;
--   3. for every fast finite-energy plane $f$ asymptotic to $P$ at $\infty$ that is $\varepsilon$-close to $u$ in the sense of `IsCylCloseTo`, there are a homeomorphism $\psi$ of $\mathbb{C}$, smooth with smooth inverse, a smooth $v : \mathbb{C} \to B_\rho(0)$, $\kappa \in \mathbb{C} \setminus \{0\}$ and $b' > 0$ with
--      - $f(z) = \Phi(\psi(z), v(z))$ for all $z$,
--      - $z \mapsto (\psi(z), v(z))$ is $\bar J$-holomorphic: $D(\psi, v)(z) \circ i = \bar J(\psi(z), v(z)) \circ D(\psi, v)(z)$,
--      - in the coordinates $z = e^{2\pi(s + it)}$, $\psi(z)/z - \kappa$ decays like $e^{-b's}$ and $v(z)$ decays like $e^{\delta s}$, both in $C^\infty$ (`ExpDecayCInfty`).
--
--   **Role.** A single holomorphic coordinate system around $u$ in which all fast planes over $P$ near $u$ appear, with explicit behaviour at $\infty$.
--
--   **Formalization Note.** $\mathbb{R}^4$ is `V 1` and the symplectization $\mathbb{R} \times S$ is $V_1 \setminus \{0\}$. The cylindrical coordinate is `cylInf s t`; the complex structure $i$ on the domain is `Complex.I • ContinuousLinearMap.id ℝ ℂ`. The winding condition is stated with `HasLoopEigenWind Sinf μ k → k ≤ 0`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.23-6.25); asymptotic operators and windings as in H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A tube around an embedded fast plane `u` over `P` (CZ index at least `3`) in which every fast
plane over `P` that is `ε`-close to `u` is a holomorphic graph `z ↦ Φ (ψ z, v z)`, with `ψ` a
diffeomorphism of `ℂ` asymptotic to `z ↦ κ z` and `v` decaying like `e^{δ s}` in cylindrical
coordinates; `δ < 0` and the loop eigenfunctions of `Sinf` with eigenvalue at most `δ` have
winding at most `0`. -/
theorem exists_tubeGraph_of_isCylCloseTo (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∃ ρ > 0, ∃ b > 0, ∃ (Φ : ℂ × ℂ → V 1) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
      (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1),
      ∃ δ < 0, ∃ ε > 0,
      IsStdTubeStructure ρ b Jbar Jinf Sinf ∧
      Set.InjOn Φ (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0) ∧
      ∀ f : ℂ → V 1, IsFastPlane H J f → IsNondegenerateEnd H f cylInf P 1 →
        IsCylCloseTo H ε f u →
        ∃ (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ) (κ : ℂ) (b' : ℝ),
          ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ ψ.symm ∧ ContDiff ℝ ∞ v ∧
          (∀ z, v z ∈ ball (0 : ℂ) ρ) ∧ (∀ z, f z = Φ (ψ z, v z)) ∧
          (∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
              (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
            (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)) ∧
          κ ≠ 0 ∧ 0 < b' ∧
          ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b' ∧
          ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ) := by
  sorry

end FiniteEnergyPlane
