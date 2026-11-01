-- Prove2me | Theorems.Thm_ConstrainedTrading_theorem_2_3_integral_optimizer
-- name    : ConstrainedTrading.theorem_2_3_integral_optimizer
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:03.071533+00:00
-- url     : https://prove2.me/theorems/609030fa-a7be-493c-bf13-3b199e89f272
-- title:
--   Theorem 2.3 — $\hat f$ of an M$^\sharp$-concave $f$ has an integer maximizer over an integral polymatroid
-- statement:
--   Let $E$ be a finite set, let $f:\mathbb Z^E\to\mathbb R\cup\{-\infty\}$ be M$^\sharp$-concave, and let $P=P(\rho)$ be a nonempty integral polymatroid ($\rho:2^E\to\mathbb Z$ submodular). Then problem (2),
--   $$
--   \text{maximize } \hat f(y)\quad\text{s.t. } y\in P,
--   $$
--   has an integer optimizer: there is $z\in\mathbb Z^E\cap P$ with $\hat f(y)\le\hat f(z)$ for every $y\in P$.
--
--   The paper calls this result new (special cases appear in Gul, Pesendorfer and Zhang 2019). It is the engine of Lemma 3.1 and Theorem 3.1: an integral polymatroid constraint does not destroy the integrality of the concave relaxation of an M$^\sharp$-concave maximization.
--
--   **Formalization Note** If $\hat f=-\infty$ on all of $P$, every integer point of $P$ is an optimizer.
--
--   Differences from the source:
--
--   - reading: there exists an integer optimizer for problem 2 → ∃ integer z ∈ P with objective(x) ≤ objective(z) for every x ∈ P; reason: the conclusion asserts both attainment of the maximum and integrality; under R1 P is a polytope and both hold
--   - reading: integral polymatroid P_f = {x ∈ ℝ^E : Σ_{e∈S} x_e ≤ f(S) ∀S ⊆ E} (p.4, no sign constraint) → P(ρ) = {x : x ≥ 0, Σ_{e∈S} x_e ≤ ρ(S) ∀S}; reason: standard meaning of polymatroid, outcomes are x ∈ ℤ₊^E (p.3); without x ≥ 0 the statement is false (E = {e}, ρ ≡ 0, seller valuation w(z) = −z: the objective −x is unbounded on (−∞, 0])
--   - reading: concave extension f̂(x) = max{Σ_z λ_z f(z) : Σ_z λ_z z = x, 0 ≤ λ_z ≤ 1, Σ_z λ_z = 1} (Defs 2.8–2.9, p.5) → f̂(x) = sSup over finite convex representations in EReal, sup ∅ = −∞; reason: a max need not be attained for a general f; the sup is the total version, and it is the convex-combination hull, not the closed concave closure
--   - encoding: an integral polymatroid P → hypothesis P(ρ) nonempty; reason: nondegeneracy: it only excludes P = ∅ (some ρ(S) < 0), where there is no feasible point to exhibit; when P ≠ ∅, 0 ∈ P
--   - reading: M♯-concave f : ℤ^E → R, exchange 'for all x, y ∈ B' with B unnamed (Def 2.7, p.4; p.5) → f : ℤ^E → ℝ ∪ {−∞}, exchange for x, y ∈ dom f = {z : f z ≠ −∞}; reason: the paper's valuations take values in ℝ ∪ {−∞} (p.3, footnote 3) and p.5 defines dom f; the real-valued case is dom f = ℤ^E
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Theorem 2.3, p.7; problem (2), p.6

import Mathlib
import Definitions.Def_ConstrainedTrading_MNatConcave
import Definitions.Def_ConstrainedTrading_concaveExt
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Definitions.Def_ConstrainedTrading_polymatroid

namespace ConstrainedTrading

/-- **Theorem 2.3** (Kizilkale–Vohra, *Constrained Trading Networks*, arXiv:2008.09757v1, p.7).
If `f : ℤ^E → ℝ ∪ {−∞}` is M♯-concave and `P = P(ρ)` is an integral polymatroid (with `ρ`
integer-valued submodular and `P` nonempty), then problem (2), `maximize f̂(y) s.t. y ∈ P`, has
an integer optimizer: there is `z ∈ ℤ^E ∩ P` with `f̂(y) ≤ f̂(z)` for all `y ∈ P`.

**Formalization Note** The conclusion asserts both that the maximum of `f̂` over `P` is attained
and that it is attained at an integer point. `f̂` is `concaveExt f` (values in `EReal`); if
`f̂ = −∞` on all of `P`, every integer point of `P` is an optimizer. `P(ρ)` includes `x ≥ 0`
(reading R1). Nonemptiness of `P` only excludes the case with no feasible point (it holds iff
`ρ ≥ 0`, and then `0 ∈ P`). -/
theorem theorem_2_3_integral_optimizer {E : Type*} [Fintype E] [DecidableEq E]
    (f : (E → ℤ) → WithBot ℝ) (hf : MNatConcave f) (ρ : Finset E → ℤ) (hρ : SteinitzExchange.Duality.IsSubmodular ρ)
    (hP : (polymatroid ρ).Nonempty) :
    ∃ z : E → ℤ, (fun e => (z e : ℝ)) ∈ polymatroid ρ ∧
      ∀ x ∈ polymatroid ρ, concaveExt f x ≤ concaveExt f (fun e => (z e : ℝ)) := by sorry

end ConstrainedTrading
