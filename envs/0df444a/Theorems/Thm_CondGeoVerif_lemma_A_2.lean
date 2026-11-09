-- Prove2me | Theorems.Thm_CondGeoVerif_lemma_A_2
-- name    : CondGeoVerif.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:27:39.855206+00:00
-- url     : https://prove2.me/theorems/68d68597-d2fe-48d8-a96a-ee58c111e57c
-- title:
--   Lemma A.2 — attainment, bounded duals $0\le\alpha\le1$, $\|\gamma\|\le\sqrt{2\pi}(1+\eta)<4$, measurability
-- statement:
--   Let $r\ge1$, $0<\eta<1/2$ and $G\sim N(0,I_r)$.
--   1. For every Borel $D:\mathbb R^r\to\{0,1\}$ the first-moment program is attained and
--   $$M_{1,\eta}(D)=\min_{\alpha\in\mathbb R,\ \gamma\in\mathbb R^r}\big\{\eta\alpha+\mathbb E(D(G)-\alpha-\gamma\cdot G)_+\big\},$$
--   with the minimum attained.
--   2. Every dual minimizer satisfies $0\le\alpha\le1$ and $\|\gamma\|\le\sqrt{2\pi}(1+\eta)$, and $\sqrt{2\pi}(1+\eta)<4$.
--   3. The mass-only formula is $M_{0,\eta}(D)=\min\{\eta,\mathbb ED\}$, with a dual $\alpha\in\{0,1\}$ and no $\gamma$.
--   4. For a jointly Borel family $D_\theta(g)$ on a standard Borel parameter space, $\theta\mapsto M_{1,\eta}(D_\theta)$ is Borel; dual minimizers can be chosen jointly Borel in $\theta$; for every $\zeta>0$ there is a jointly Borel choice of primal feasible $e_\theta(g)$ with objective at least $M_{1,\eta}(D_\theta)-\zeta$; and the mass-only dual $\alpha_\theta\in\{0,1\}$ can be chosen Borel in $\theta$.
--
--   The sign $\alpha\ge0$ of the scalar dual is what makes full Massart completeness possible, and the uniform bound on $\gamma$ gives the covariance bound $B=4$ of the norm tests.
--
--   Differences from the source:
--   - reading: "In particular one may restrict minimization to the fixed compact set K_r = [0,1] × {‖γ‖ ≤ 4}" → not a separate clause; reason: it follows from the attained minimum and the bounds on every minimizer, which are stated
--   - reading: "with a Borel dual α ∈ {0, 1}" for the mass-only program → a {0,1}-valued minimizing dual for each D, and one chosen Borel in the parameter for every jointly Borel family; reason: the stronger of the two readings of "Borel dual"
--   - encoding: allocations 0 ≤ e ≤ 1 in L^∞(N(0, I_r)); D with values in {0,1} → Borel functions with values in [0,1] everywhere; D Boolean, used through its 0/1 indicator; reason: every such L^∞ class has such a representative; same programs
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Lemma A.2, p.14 (PDF p.17)

import Mathlib
import Definitions.Def_CondGeoVerif_Mprog

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **Lemma A.2 (Attainment, bounded duals, and measurability)** (Chen, *The Conditional Geometry
of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, p.14 = PDF p.17). Let
`r ≥ 1` and `0 < η < 1/2` (the standing noise bound of §A.1).
1. For every Borel `D : ℝʳ → {0, 1}` the first-moment program is attained, and
   `M_{1,η}(D) = min_{α ∈ ℝ, γ ∈ ℝʳ} {ηα + E(D(G) − α − γ·G)₊}` with the minimum attained.
2. Every dual minimizer satisfies `0 ≤ α ≤ 1` and `‖γ‖ ≤ √(2π)(1 + η)`, and `√(2π)(1 + η) < 4`.
3. The mass-only program is `M_{0,η}(D) = min{η, ED}`, with a dual `α ∈ {0, 1}` and no `γ`.
4. For a jointly Borel family `D_θ(g)` on a standard Borel parameter space, `θ ↦ M_{1,η}(D_θ)` is
   Borel, dual minimizers can be chosen jointly Borel in `θ`, for every `ζ > 0` there is a jointly
   Borel primal feasible `e_θ(g)` with objective at least `M_{1,η}(D_θ) − ζ`, and the mass-only
   dual `α_θ ∈ {0, 1}` can be chosen Borel in `θ`.

**Formalization Note** The mass-only dual objective is `dualObj η D α 0` (no `γ`). The clause
"one may restrict minimization to `K_r = [0, 1] × {‖γ‖ ≤ 4}`" follows from 1 and 2 and is not
restated. -/
theorem lemma_A_2 {r : ℕ} (hr : 1 ≤ r) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    (∀ D : Vec r → Bool, Measurable D →
      (∃ e ∈ errorAllocs 1 η r, ∫ z, e z * ind (D z) ∂(gauss r) = Mprog 1 η D) ∧
      (∃ (α : ℝ) (γ : Vec r), IsDualMin η D α γ ∧ Mprog 1 η D = dualObj η D α γ) ∧
      (∀ (α : ℝ) (γ : Vec r), IsDualMin η D α γ →
        0 ≤ α ∧ α ≤ 1 ∧ ‖γ‖ ≤ Real.sqrt (2 * Real.pi) * (1 + η)) ∧
      Mprog 0 η D = min η (gauss r {z | D z = true}).toReal ∧
      (∃ α ∈ ({0, 1} : Set ℝ), (∀ α' : ℝ, dualObj η D α 0 ≤ dualObj η D α' 0) ∧
        Mprog 0 η D = dualObj η D α 0)) ∧
    Real.sqrt (2 * Real.pi) * (1 + η) < 4 ∧
    (∀ (Θ : Type) [MeasurableSpace Θ] [StandardBorelSpace Θ] (D : Θ → Vec r → Bool),
      Measurable (fun p : Θ × Vec r => D p.1 p.2) →
        Measurable (fun θ => Mprog 1 η (D θ)) ∧
        (∃ (α : Θ → ℝ) (γ : Θ → Vec r), Measurable α ∧ Measurable γ ∧
          ∀ θ, IsDualMin η (D θ) (α θ) (γ θ)) ∧
        (∀ ζ : ℝ, 0 < ζ → ∃ e : Θ → Vec r → ℝ, Measurable (fun p : Θ × Vec r => e p.1 p.2) ∧
          ∀ θ, e θ ∈ errorAllocs 1 η r ∧
            Mprog 1 η (D θ) - ζ ≤ ∫ z, e θ z * ind (D θ z) ∂(gauss r)) ∧
        (∃ α : Θ → ℝ, Measurable α ∧ ∀ θ, α θ ∈ ({0, 1} : Set ℝ) ∧
          (∀ α' : ℝ, dualObj η (D θ) (α θ) 0 ≤ dualObj η (D θ) α' 0) ∧
          Mprog 0 η (D θ) = dualObj η (D θ) (α θ) 0)) := by sorry

end CondGeoVerif
