-- Prove2me | Theorems.Thm_BERicci_Energy_theorem_3_14
-- name    : BERicci.Energy.theorem_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:00.754095+00:00
-- url     : https://prove2.me/theorems/3cd75d40-fec6-4556-a4c1-4bd375520ef9
-- title:
--   Theorem 3.14, p. 38 — on an Energy measure space E = 2Ch (3.40) iff E is upper-regular; then 𝔾 = 𝕍
-- statement:
--   Let $(X,\tau,m,\mathcal E)$ be an Energy measure space (Definition 3.6) and let $\mathrm{Ch}$ be the Cheeger energy of the metric measure space $(X,d_{\mathcal E},m)$. Then
--
--   $$\mathcal E(f)=2\,\mathrm{Ch}(f)\qquad\text{for every }f\in L^2(X,m)\tag{3.40}$$
--
--   if and only if $\mathcal E$ is upper-regular (Definition 3.13). In this case $\mathbb G=\mathbb V$: every $f\in\mathbb V$ admits a carré du champ $\Gamma(f)$.
--
--   The theorem identifies the Dirichlet forms that are canonically produced by their own intrinsic distance: an Energy measure space is the energy of a metric measure space exactly when its form is upper-regular. It is the bridge from the Dirichlet-form side ($BE(K,N)$) to the metric side ($\mathrm{RCD}(K,\infty)$) used in the main theorem of the paper.
--
--   **Formalization Note** The metric of $X$ is $d_{\mathcal E}$ (condition (b) of Definition 3.6), so the Cheeger energy is computed with the slope of that metric. Both $\mathcal E$ and $\mathrm{Ch}$ take the value $\infty$ off $L^2$. "Dense subset of $\mathbb V$" in upper regularity is density for the norm of $\mathbb V$, and the dense subset cannot be empty or trivial. The Cheeger energy is defined from slopes of bounded Lipschitz functions, independently of $\mathcal E$. The remaining assertions of Theorem 3.14, (3.41), the density of $\mathbb V\cap\mathrm{Lip}_b$ and mass preservation, are separate items of this mission.
-- source:
--   arXiv:1209.5786v4, Theorem 3.14, (3.40), p. 38

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 3.14** (p. 38): on an Energy measure space, `E(f) = 2 Ch(f)` for every `f ∈ L²(X, m)` (3.40),
`Ch` the Cheeger energy of `(X, d_E, m)`, iff `E` is upper-regular; in this case `𝔾 = 𝕍`. -/
theorem theorem_3_14 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hEMS : BERicci.Gamma.IsEnergyMeasureSpace m E S) :
    ((∀ f : X → ℝ, MemLp f 2 m → E f = 2 * BERicci.Gamma.cheeger m f) ↔ BERicci.Gamma.IsUpperRegular m E) ∧
    (BERicci.Gamma.IsUpperRegular m E → ∀ f : X → ℝ, E f < ⊤ → ∃ g : X → ℝ, BERicci.Gamma.IsCarreDuChamp m E f g) := by sorry

end BERicci.Energy
