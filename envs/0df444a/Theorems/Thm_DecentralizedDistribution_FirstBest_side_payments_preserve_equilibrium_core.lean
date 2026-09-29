-- Prove2me | Theorems.Thm_DecentralizedDistribution_FirstBest_side_payments_preserve_equilibrium_core
-- name    : DecentralizedDistribution.FirstBest.side_payments_preserve_equilibrium_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T07:01:08.12062+00:00
-- url     : https://prove2.me/theorems/b0d451f2-aa06-471b-ad65-45f62247c27f
-- title:
--   Theorem 5.1 — side payments move the allocations at an equilibrium into the core without changing the equilibria
-- statement:
--   Let demand have a probability law $\mu$ under which all demands are nonnegative almost surely. Let AR-$m$ be an allocation rule whose profits $P^m_n([Z],\cdot)$ are integrable for every nonnegative profile $[Z]$, and let $[Z]^{m*}$ be a pure-strategy Nash equilibrium of the inventory game under AR-$m$. Then there exist side payments $w_n([Z]^{m*},\vec D)$, depending only on $[Z]^{m*}$ and the demand realization and integrable in $\vec D$, such that the rule AR-$\tilde m$ with
--   $$\alpha^{\tilde m}_n([Z],\vec D)=\alpha^m_n([Z],\vec D)+w_n([Z]^{m*},\vec D)$$
--   satisfies
--   1. AR-$\tilde m$ and AR-$m$ have exactly the same pure-strategy Nash equilibria; in particular $[Z]^{m*}$ is one;
--   2. at $[Z]=[Z]^{m*}$ the allocations of AR-$\tilde m$ lie in the core of SAG$([Z]^{m*},\vec D)$ for every demand realization $\vec D$.
--
--   Demand-dependent side payments that do not depend on the players' choices thus make any allocation rule's allocations at its equilibrium ex-post stable without changing incentives.
--
--   **Formalization Note.** The paper assumes that the $J^m_n$ are continuous and "unimodular" so that a pure equilibrium exists; since $[Z]^{m*}$ is given here as a hypothesis, that assumption is not needed and is omitted. The paper's conclusion "$[Z]^{\tilde m*}=[Z]^{m*}$" is stated as equality of the two equilibrium sets. Integrability of the profits (implicit in "$J^m_n$ is the profit function") and almost-sure nonnegativity of demand (demands are quantities) are the added hypotheses that make the expectations of the side payments finite; integrability of $w$ is part of the conclusion.
-- source:
--   Anupindi, Bassok & Zemel, A General Framework for the Study of Decentralized Distribution Systems, MSOM 3(4) 2001, p. 361, Theorem 5.1; proof p. 367

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_Game

open MeasureTheory Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- Theorem 5.1 (p. 361). Let demand be a.e. nonnegative, let AR-m be an allocation rule whose
payoffs `P^m_n([Z], ·)` are integrable for every nonnegative profile, and let `[Z]^{m*}` be a
pure-strategy Nash equilibrium under AR-m. Then there are side payments `w_n(D⃗)` (depending on
`[Z]^{m*}` and `D⃗` only), integrable in `D⃗`, such that the rule AR-m̃,
`α^{m̃}_n([Z], D⃗) = α^m_n([Z], D⃗) + w_n(D⃗)`, has (i) exactly the same Nash equilibria as AR-m,
and (ii) at `[Z]^{m*}` allocations in the core of SAG([Z]^{m*}, D⃗) for every `D⃗`. -/
theorem side_payments_preserve_equilibrium_core {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) [IsProbabilityMeasure μ]
    (hD : ∀ᵐ D ∂μ, ∀ n, 0 ≤ D n)
    (α : AllocationRule N W)
    (hα : ∀ Z : Profile N W, Z.Nonneg → ∀ n, Integrable (fun D => payoff sys α Z D n) μ)
    (Zm : Profile N W) (hZm : IsNashEquilibrium sys μ α Zm) :
    ∃ w : Fin N → Demand N → ℝ, (∀ n, Integrable (w n) μ) ∧
      (∀ Z : Profile N W,
        IsNashEquilibrium sys μ (fun Z' D n => α Z' D n + w n D) Z ↔ IsNashEquilibrium sys μ α Z) ∧
      ∀ D : Demand N,
        (fun n => α Zm D n + w n D) ∈ Core Finset.univ (fun S => coalitionValue sys S Zm D) := by sorry

end DecentralizedDistribution.FirstBest
