-- Prove2me | Theorems.Thm_FairRandomObject_Bads_prop_14_support
-- name    : FairRandomObject.Bads.prop_14_support
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:35.37402+00:00
-- url     : https://prove2.me/theorems/8019e1be-b936-4bf0-a7df-8567b80fbb74
-- title:
--   Proof of Proposition 14, p. 25 — Fair Share gives a supporting vector α with ϕ_1(x)x_1 ≤ α·(x − e^N) + 1/n
-- statement:
--   Let $n\ge2$ and let $\varphi$ be a symmetric API rule for a bad that satisfies Fair Share. Then there is a vector $\alpha\in\mathbb R^N$ such that, for agent $1$,
--   $$\varphi_1(x)\,x_1\le\alpha\cdot(x-e^N)+\frac1n\qquad\text{for all }x\in\mathbb R^N_+ .$$
--
--   In the paper this is the supporting hyperplane, at $e^N$, of the concavification of $f(x)=\varphi_1(x)x_1$, which coincides with $f$ at $e^N$ because of Fair Share. It is the first step of the "only if" direction of Proposition 14.
--
--   **Formalization Note** The paper's agent $1$ is agent `0 : Fin n`.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, proof of Proposition 14

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting

namespace FairRandomObject.Bads

open MeasureTheory

/-- Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, proof of Proposition 14 ("only if"): for a symmetric API rule `ϕ`
satisfying Fair Share for a bad, the concavification of `f(x) = ϕ_1(x) · x_1` coincides with
`f` at `e^N`, and some `α ∈ ℝ^N` supports its graph at `(e^N, 1/n)`:
`ϕ_1(x) · x_1 ≤ α · (x − e^N) + 1/n` for all `x ∈ ℝ^N_+`.

**Formalization Note.** The paper's agent `1` is `⟨0, _⟩ : Fin n`. The concavification `g` is not
mentioned: the statement is the supporting inequality it yields. -/
theorem prop_14_support {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ)
    (hsym : IsSymmetric ϕ) (hfs : FairShareBad ϕ) :
    ∃ α : Fin n → ℝ, ∀ x : Fin n → ℝ, 0 ≤ x →
      ϕ x ⟨0, by omega⟩ * x ⟨0, by omega⟩ ≤ α ⬝ᵥ (x - eN n) + 1 / n := by sorry

end FairRandomObject.Bads
