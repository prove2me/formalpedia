-- Prove2me | Theorems.Thm_BERicci_Energy_theorem_3_14_density
-- name    : BERicci.Energy.theorem_3_14_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:09.043087+00:00
-- url     : https://prove2.me/theorems/bf738c82-7a6f-4cb3-91dd-950c26528e2d
-- title:
--   Theorem 3.14 (density), p. 38 — for upper-regular E, 𝕍 ∩ Lip_b(X, d_E) is dense in 𝕍
-- statement:
--   Let $(X,\tau,m,\mathcal E)$ be an Energy measure space with $\mathcal E$ upper-regular. Then the space $\mathbb V\cap\mathrm{Lip}_b(X,d_{\mathcal E})$ of bounded $d_{\mathcal E}$-Lipschitz functions of finite energy is dense in $\mathbb V$: for every $f\in\mathbb V$ and $\varepsilon>0$ there is $h\in\mathbb V\cap\mathrm{Lip}_b(X,d_{\mathcal E})$ with
--
--   $$\|f-h\|_{L^2(X,m)}<\varepsilon,\qquad \mathcal E(f-h)<\varepsilon.$$
--
--   Bounded Lipschitz functions are therefore a core for the Dirichlet form, which is what makes metric approximation arguments available in $\mathbb V$.
--
--   **Formalization Note** Density is taken for the norm $(\|f\|_2^2+\mathcal E(f))^{1/2}$ of $\mathbb V$, the reading the series uses for Definition 3.13 as well; the two smallness conditions are stated separately, which is equivalent.
-- source:
--   arXiv:1209.5786v4, Theorem 3.14, p. 38

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 3.14** (p. 38): if `E` is upper-regular, `𝕍 ∩ Lip_b(X, d_E)` is dense in `𝕍` for the norm
`(‖f‖₂² + E(f))^{1/2}`. -/
theorem theorem_3_14_density {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hEMS : BERicci.Gamma.IsEnergyMeasureSpace m E S)
    (hUR : BERicci.Gamma.IsUpperRegular m E) (f : X → ℝ) (hf : E f < ⊤) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ h : X → ℝ, BERicci.Gamma.IsLipB h ∧ E h < ⊤ ∧ eLpNorm (f - h) 2 m < ε ∧ E (f - h) < ε := by sorry

end BERicci.Energy
