-- Prove2me | Theorems.Thm_FRouting_theorem_1_9
-- name    : FRouting.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:27.384163+00:00
-- url     : https://prove2.me/theorems/2e2632ee-2e9d-4729-b893-f29daafa1daa
-- title:
--   Theorem 1.9 — the fidelity $F_0$ determines $f$
-- statement:
--   Let $d\ge2$ and $\varepsilon\ge0$. If a routing strategy is $(1-\varepsilon)$-correct on input $(x,y)$, with mid-protocol state $\rho^{xy}$ and $F_0(x,y)=F(\rho^{xy}_{\bar QA},\rho^{xy}_{\bar Q}\otimes\rho^{xy}_A)$, then
--
--   1. $f(x,y)=1$ implies $F_0(x,y)\ge1-4\varepsilon$;
--   2. $f(x,y)=0$ implies $F_0(x,y)\le\frac12+\sqrt{2\varepsilon}$.
--
--   The mid-protocol state can be prepared without knowing $f(x,y)$, so this reduces evaluating $f$ to estimating a fidelity.
--
--   Differences from the source:
--   - generalization: stated in the overview at d = 2 (p.5) → every d ≥ 2, with the bound 1/2; reason: p.5 says the full results hold for arbitrary d, and 1/d ≤ 1/2 as on p.22; d = 2 is an instance
--   - generalization: all registers d-dimensional qudits, and the resource prepared by a channel on |0^{2q}⟩ (§3.4) → any finite registers L, R, A₁, A₂, B₁, B₂ and any density matrix on LR, with Q, Q̄, Q₀, Q₁ of dimension d; reason: the statement needs only that they are finite; tuples of qudits and prepared resources are the special case
--   - encoding: ε with no stated sign → 0 ≤ ε; reason: ε < 0 makes correctness ≥ 1 − ε unsatisfiable, and it would make √(2ε) a junk value
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 1.9, p.6

import Definitions.Def_FRouting_RoutingStrategy

set_option autoImplicit false

namespace FRouting

/-- **Theorem 1.9.** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 1.9, p.6: "Let a routing strategy be (1 − ε)-correct on input (x, y),
and let ρ^{xy}_{Q̄AB} be its mid-protocol state. Define F₀(x, y) := F(ρ^{xy}_{Q̄A}, ρ^{xy}_{Q̄} ⊗ ρ^{xy}_A).
Then f(x, y) = 1 ⟹ F₀(x, y) ≥ 1 − 4ε, f(x, y) = 0 ⟹ F₀(x, y) ≤ 1/2 + √(2ε)."

**Formalization Note** The page is in an overview at `d = 2` (p.5). The statement here is for every
`d ≥ 2`, using `1/d ≤ 1/2` (as p.22 does). The second clause is Lemma 4.3 with Alice and Bob
exchanged, which Theorem 4.1 does not print. -/
theorem theorem_1_9 {n d : ℕ} (hd : 2 ≤ d) (S : RoutingStrategy n d)
    (f : (Fin n → Bool) → (Fin n → Bool) → Bool) (ε : ℝ) (hε : 0 ≤ ε) (x y : Fin n → Bool)
    (hc : S.IsCorrectOn f ε x y) :
    (f x y = true → 1 - 4 * ε ≤ S.F0 x y) ∧
    (f x y = false → S.F0 x y ≤ 1 / 2 + Real.sqrt (2 * ε)) := by sorry

end FRouting
