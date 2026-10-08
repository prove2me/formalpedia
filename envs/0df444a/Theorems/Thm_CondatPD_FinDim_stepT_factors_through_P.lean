-- Prove2me | Theorems.Thm_CondatPD_FinDim_stepT_factors_through_P
-- name    : CondatPD.FinDim.stepT_factors_through_P
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:40:27.935997+00:00
-- url     : https://prove2.me/theorems/27768ba9-f312-4faa-85b2-b6155226c1b5
-- title:
--   §4, proof of Theorem 3.3, p. 12, (32)–(33) — T depends on z only through Pz (T ∘ S = T)
-- statement:
--   Let $\tau>0$, $\sigma>0$, $L:\mathcal X\to\mathcal Y$ bounded linear, and let $\mathrm{prox}_{\tau G}$, $\mathrm{prox}_{\sigma H^*}$ be arbitrary maps. Let $T:\mathcal X\times\mathcal Y\to\mathcal X\times\mathcal Y$ be the operator $T(x,y)=(\tilde x,\tilde y)$ with
--   $$\tilde x=\mathrm{prox}_{\tau G}(x-\tau L^*y),\qquad \tilde y=\mathrm{prox}_{\sigma H^*}\big(y+\sigma L(2\tilde x-x)\big),$$
--   and $P(x,y)=(\tfrac1\tau x-L^*y,\,-Lx+\tfrac1\sigma y)$ the operator (20). Then for all $z,z'\in\mathcal X\times\mathcal Y$,
--   $$Pz=Pz'\ \Longrightarrow\ T(z)=T(z').$$
--
--   Writing $(u,v)=P(x,y)$, one has $\tilde x=\mathrm{prox}_{\tau G}(\tau u)$ and $\tilde y=\mathrm{prox}_{\sigma H^*}(2\sigma L\tilde x+\sigma v)$, the rewriting (32)–(33). Since $P$ is self-adjoint, $\operatorname{ran}P=(\ker P)^\perp$, so for the orthogonal projector $S$ onto $\operatorname{ran}P$ one has $Sz=Sz'$ iff $Pz=Pz'$; the statement is therefore the paper's identity $T\circ S=T$.
--
--   **Formalization Note** The projector $S$ is not built; the equivalent form "$T$ factors through $P$" is stated. The hypotheses $\tau>0$, $\sigma>0$ are the algorithm's standing choice and are needed: at $\tau=0$ the claim fails.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 12, §4, proof of Theorem 3.3 for Algorithm 3.1, (32)–(33)

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

open InnerProductSpace

namespace CondatPD.FinDim

/-- Proof of Theorem 3.3, (32)–(33) (p. 12): `T` depends on `z` only through `P z`, i.e.
`T ∘ S = T` for the orthogonal projector `S` onto `ran(P) = (ker P)^⊥`. -/
theorem stepT_factors_through_P {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (PG : X → X) (PH : Y → Y) (L : X →L[ℝ] Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) :
    ∀ z z' : X × Y, opP τ σ L z = opP τ σ L z' →
      stepT PG PH τ σ L z = stepT PG PH τ σ L z' := by sorry

end CondatPD.FinDim
