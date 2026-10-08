-- Prove2me | Theorems.Thm_CondatPD_FinDim_stepT_continuous
-- name    : CondatPD.FinDim.stepT_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:40:56.345761+00:00
-- url     : https://prove2.me/theorems/9742c672-833b-4590-b8c4-81b46dacdc24
-- title:
--   §4, proof of Theorem 3.3, p. 13 — the operator T is continuous
-- statement:
--   Let $G\in\Gamma_0(\mathcal X)$, $H\in\Gamma_0(\mathcal Y)$, $L:\mathcal X\to\mathcal Y$ bounded linear, $\tau>0$, $\sigma>0$, and let $\mathrm{prox}_{\tau G}$, $\mathrm{prox}_{\sigma H^*}$ be the proximity operators. Then the operator
--   $$T:(x,y)\mapsto(\tilde x,\tilde y),\qquad \tilde x=\mathrm{prox}_{\tau G}(x-\tau L^*y),\quad\tilde y=\mathrm{prox}_{\sigma H^*}\big(y+\sigma L(2\tilde x-x)\big),$$
--   is continuous on $\mathcal X\times\mathcal Y$.
--
--   Continuity of $T$ transfers the convergence of the shadow sequence $(z'_n)$ to the sequence $(\tilde z_n)$ in the proof of Theorem 3.3.
--
--   **Formalization Note** Finite dimension is not assumed.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 13, §4, proof of Theorem 3.3 for Algorithm 3.1, before (43)

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

open InnerProductSpace

namespace CondatPD.FinDim

/-- Proof of Theorem 3.3 (p. 13): `T` is continuous, by continuity of the proximity operators
`prox_{τG}` and `prox_{σH*}`. -/
theorem stepT_continuous {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ)
    (PG : X → X) (PH : Y → Y)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH) :
    Continuous (stepT PG PH τ σ L) := by sorry

end CondatPD.FinDim
