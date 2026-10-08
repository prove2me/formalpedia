-- Prove2me | Theorems.Thm_BERicci_Energy_theorem_3_14_gradient
-- name    : BERicci.Energy.theorem_3_14_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:52.866982+00:00
-- url     : https://prove2.me/theorems/d95e41ba-f088-45bc-91bb-fddc2eabd83e
-- title:
--   Theorem 3.14, (3.41), p. 38 — for upper-regular E, every f ∈ 𝕍 has a minimal weak gradient and Γ(f) = |Df|²_w
-- statement:
--   Let $(X,\tau,m,\mathcal E)$ be an Energy measure space and suppose that $\mathcal E$ is upper-regular (Definition 3.13). Then every $f\in\mathbb V$ has a minimal weak gradient $|Df|_w$ with respect to $d_{\mathcal E}$, and its carré du champ satisfies
--
--   $$\Gamma(f)=|Df|_w^2\qquad m\text{-a.e. in }X\ \text{for every }f\in\mathbb V.\tag{3.41}$$
--
--   The identity says that, for upper-regular forms, the energy density of the Dirichlet form is the squared metric gradient of the intrinsic distance, pointwise almost everywhere.
--
--   **Formalization Note** "Γ(f) = |Df|²_w" is stated in two parts: a minimal weak gradient of $f$ exists, and every carré du champ density of $f$ equals the square of every minimal weak gradient $m$-a.e. The existence of the carré du champ ($\mathbb G=\mathbb V$) is part of the goal theorem.
-- source:
--   arXiv:1209.5786v4, Theorem 3.14, (3.41), p. 38

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 3.14** (p. 38), (3.41): if `E` is upper-regular, every `f ∈ 𝕍` has a minimal weak gradient and
`Γ(f) = |Df|_w²` m-a.e. -/
theorem theorem_3_14_gradient {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hEMS : BERicci.Gamma.IsEnergyMeasureSpace m E S)
    (hUR : BERicci.Gamma.IsUpperRegular m E) (f : X → ℝ) (hf : E f < ⊤) :
    (∃ w : X → ℝ, IsMinWeakGrad m f w) ∧
    ∀ g w : X → ℝ, BERicci.Gamma.IsCarreDuChamp m E f g → IsMinWeakGrad m f w →
      g =ᵐ[m] fun x => w x ^ 2 := by sorry

end BERicci.Energy
