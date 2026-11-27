-- Prove2me | Theorems.Thm_EquivalencePrinciple_spacetime_universality
-- name    : EquivalencePrinciple.spacetime_universality
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T00:57:10.274252+00:00
-- url     : https://prove2.me/theorems/71463164-0c1b-50d7-9585-faecdcf31188
-- title:
--   Weak equivalence principle: universality of free fall (geodesic form)
-- statement:
--   **The weak equivalence principle, spacetime (metric-theory) form.**
--
--   Let `S` be a metric spacetime and let `γ`, `δ` be two freely falling worldlines in `S`: twice continuously differentiable curves $\mathbb{R} \to \mathbb{R}^4$ satisfying the geodesic equation
--
--   $$\gamma''^k = -\sum_{i,j} \Gamma^k_{ij}(\gamma)\, \gamma'^i\, \gamma'^j \quad \text{for every } t,$$
--
--   with the Christoffel symbols of the spacetime. Assume they are **launched at the same event with the same velocity**: $\gamma(t_0) = \delta(t_0)$ and $\gamma'(t_0) = \delta'(t_0)$ at some time $t_0$.
--
--   **Conclusion:** the worldlines coincide for all time: $\gamma(t) = \delta(t)$ for every $t$.
--
--   In words: in a metric theory of gravity, freely falling test particles with the same initial position and velocity follow the same worldline — no mass, charge, composition or other property of the particle appears anywhere in the geodesic equation. This is the spacetime reading of "all uncharged, freely falling test particles follow the same trajectories, once an initial position and velocity have been prescribed", and it is what makes "trajectories of freely falling bodies are geodesics of symmetric metric" a universality statement.
--
--   **Formalization note.** The geodesic right-hand side depends on the worldline through both $\gamma$ and $\gamma'$, so the uniqueness argument runs on the first-order system $(\gamma, \gamma')$; the needed local Lipschitz property of the Christoffel symbols follows from the twice continuous differentiability of the metric. The statement is global in time (true, by continuation).
-- source:
--   Wikipedia, Equivalence principle, https://en.wikipedia.org/wiki/Equivalence_principle (source of the quoted statements, reproduced verbatim in the definition file) ('All uncharged, freely falling test particles follow the same trajectories, once an initial position and velocity have been prescribed'; 'trajectories of freely falling bodies are geodesics of symmetric metric')

import Mathlib
import Definitions.Def_EquivalencePrinciple

namespace EquivalencePrinciple

/-- Milestone: the weak equivalence principle in its spacetime (metric-theory)
form.  Two freely falling test particles in the same spacetime, launched at the
same event with the same velocity, follow the same worldline for all time: the
geodesic equation `γ'' = -Γ(γ)(γ', γ')` contains no property of the particle
— no mass, charge or composition — so equal initial data determine the same
solution. -/
theorem spacetime_universality (S : Spacetime) (γ δ : ℝ → Sp)
    (hγ : IsFreelyFalling S γ) (hδ : IsFreelyFalling S δ)
    (t₀ : ℝ) (hpos : γ t₀ = δ t₀) (hvel : deriv γ t₀ = deriv δ t₀) :
    ∀ t : ℝ, γ t = δ t := by
  sorry

end EquivalencePrinciple
