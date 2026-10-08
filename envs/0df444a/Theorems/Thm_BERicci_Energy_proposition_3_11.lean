-- Prove2me | Theorems.Thm_BERicci_Energy_proposition_3_11
-- name    : BERicci.Energy.proposition_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:40.89761+00:00
-- url     : https://prove2.me/theorems/fde07423-a5ba-40b2-807e-a86726cdb27a
-- title:
--   Proposition 3.11, p. 35 — f ∈ 𝔾 ∩ C_b(X) with Γ(f) ≤ ζ² is d_E-Lipschitz, |D*f| ≤ ζ, and ζ is an upper gradient of f
-- statement:
--   Let $(X,\tau,m,\mathcal E)$ be an Energy measure space. Let $f\in\mathbb G\cap C_b(X)$ be a bounded continuous function with carré du champ $\Gamma(f)$, and let $\zeta:X\to[0,\infty)$ be bounded and upper semicontinuous with
--
--   $$\Gamma(f)\le\zeta^2\qquad m\text{-a.e. in }X.$$
--
--   Then:
--
--   1. $f$ is Lipschitz with respect to $d_{\mathcal E}$;
--   2. $|D^*f|(x)\le\zeta(x)$ for every $x\in X$;
--   3. $\zeta$ is an upper gradient of $f$ in the sense of (3.3).
--
--   The proposition turns an $m$-a.e. bound on the energy density into a pointwise bound on the metric slope. It is the step of Theorem 3.14 that converts the upper-semicontinuous majorants of Definition 3.13 into bounds on $|Df_n|$, hence on the Cheeger energy.
--
--   **Formalization Note** $f$ itself (not a representative) is continuous and bounded. The hypothesis $\Gamma(f)\le\zeta^2$ is stated as the existence of a carré du champ density $g$ of $f$ with $g\le\zeta^2$ $m$-a.e.; this also gives $f\in\mathbb G$, and the density is unique $m$-a.e. The asymptotic Lipschitz constant takes values in $[0,\infty]$ and is compared with $\zeta(x)$ there.
-- source:
--   arXiv:1209.5786v4, Proposition 3.11, p. 35

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Proposition 3.11** (p. 35): `f ∈ 𝔾 ∩ C_b(X)` with `Γ(f) ≤ ζ²` m-a.e. for a bounded upper semicontinuous
`ζ ≥ 0` is Lipschitz for `d_E`, `|D*f| ≤ ζ` everywhere, and `ζ` is an upper gradient of `f` (3.3). -/
theorem proposition_3_11 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hEMS : BERicci.Gamma.IsEnergyMeasureSpace m E S)
    (f ζ : X → ℝ) (hfc : Continuous f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hζ0 : ∀ x, 0 ≤ ζ x) (hζb : ∃ C : ℝ, ∀ x, ζ x ≤ C) (hζu : UpperSemicontinuous ζ)
    (hΓ : ∃ g : X → ℝ, BERicci.Gamma.IsCarreDuChamp m E f g ∧ ∀ᵐ x ∂m, g x ≤ ζ x ^ 2) :
    (∃ K, LipschitzWith K f) ∧ (∀ x, BERicci.Gamma.slopeStar f x ≤ ENNReal.ofReal (ζ x)) ∧ IsUpperGradient ζ f := by sorry

end BERicci.Energy
