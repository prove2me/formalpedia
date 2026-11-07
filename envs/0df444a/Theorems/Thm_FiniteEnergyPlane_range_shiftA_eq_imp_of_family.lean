-- Prove2me | Theorems.Thm_FiniteEnergyPlane_range_shiftA_eq_imp_of_family
-- name    : FiniteEnergyPlane.range_shiftA_eq_imp_of_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T15:14:54.638827+00:00
-- url     : https://prove2.me/theorems/76e27300-da56-4acd-b965-20cdeaa37a04
-- title:
--   Translates of the members of a family through an embedded plane have different images
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on the contact planes, and let $P$ be a periodic Reeb orbit. Let $u : \mathbb{C} \to V_1$ be an embedded plane avoiding $0$ and asymptotic to $P$ at $\infty$. Let $g : \mathbb{C} \times (-r, r) \to V_1$ be $C^1$ with $g(\cdot, 0) = u$, avoiding $0$, such that:
--
--   1. for every $\varepsilon > 0$ there is $r' \in (0, r]$ with $g(\cdot, t)$ $\varepsilon$-close to $u$ in the sense of `IsCylCloseTo` for all $|t| < r'$;
--   2. the identity $Dg(0, 0)(\Delta, \delta t) + \lambda\, g(0, 0) = 0$ forces $\Delta = 0$, $\delta t = 0$ and $\lambda = 0$.
--
--   Then there is $r' \in (0, r]$ such that for $c, t, c', t' \in (-r', r')$, equal images of $e^{2c} g(\cdot, t)$ and $e^{2c'} g(\cdot, t')$ force $c = c'$ and $t = t'$.
--
--   **Role.** It separates the $\mathbb{R}$-translates of the members of such a family.
--
--   **Formalization Note.** The translate is `shiftA c`. No holomorphy is assumed.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemma 6.10 and Lemma 6.20

import Definitions.Def_FiniteEnergyPlane_CylClose

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Translates of the members of a family through an embedded plane have different images. Let `u`
be an embedded plane avoiding `0` and asymptotic to `P` at `∞`, and let `g : ℂ × (-r, r) → V 1` be
`C¹` with `g(·, 0) = u`, avoiding `0`, with `g(·, t)` tending to `u` in the sense of `IsCylCloseTo`
as `t → 0`, and such that `Dg(0, 0)(Δ, δt) + λ • g(0, 0) = 0` forces `Δ = 0`, `δt = 0`, `λ = 0`.
Then for some `r' ∈ (0, r]` the images of `e^{2c} • g(·, t)`, `(c, t) ∈ (-r', r')²`, are pairwise
different: equal images force equal parameters. -/
theorem range_shiftA_eq_imp_of_family (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u)
    (r : ℝ) (hr : 0 < r) (g : ℂ × ℝ → V 1) (hg : ContDiffOn ℝ 1 g (Set.univ ×ˢ Set.Ioo (-r) r))
    (hg0 : ∀ z, g (z, 0) = u z) (hne : ∀ t ∈ Set.Ioo (-r) r, ∀ z, g (z, t) ≠ 0)
    (hclose : ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
      IsCylCloseTo H ε (fun z => g (z, t)) u)
    (htr : ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, 0) (Δ, δt) + lam • g (0, 0) = 0 →
      Δ = 0 ∧ δt = 0 ∧ lam = 0) :
    ∃ r' ∈ Set.Ioc 0 r, ∀ c ∈ Set.Ioo (-r') r', ∀ t ∈ Set.Ioo (-r') r',
      ∀ c' ∈ Set.Ioo (-r') r', ∀ t' ∈ Set.Ioo (-r') r',
        Set.range (shiftA c (fun z => g (z, t))) = Set.range (shiftA c' (fun z => g (z, t'))) →
          c = c' ∧ t = t' := by
  sorry

end FiniteEnergyPlane
