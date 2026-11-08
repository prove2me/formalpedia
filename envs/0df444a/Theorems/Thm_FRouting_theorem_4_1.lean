-- Prove2me | Theorems.Thm_FRouting_theorem_4_1
-- name    : FRouting.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:15.244123+00:00
-- url     : https://prove2.me/theorems/0027fe51-fed9-4a9b-9266-4b1505f07157
-- title:
--   Theorem 4.1 — the universal fidelity gap
-- statement:
--   Let $d\ge2$ and $\varepsilon\ge0$. Consider a routing strategy that is $(1-\varepsilon)$-correct on an input $(x,y)$ with $f(x,y)=1$, with mid-protocol state $\rho$, and let $F_0=F(\rho_{\bar QA},\rho_{\bar Q}\otimes\rho_A)$, $F_1=F(\rho_{\bar QB},\rho_{\bar Q}\otimes\rho_B)$. Then
--   $$F_0\ge1-4\varepsilon,\qquad F_1\le\frac1d+\sqrt{2\varepsilon}.$$
--
--   No resource bound on the strategy is assumed.
--
--   Differences from the source:
--   - generalization: ε > 0 → 0 ≤ ε; reason: the proof works at ε = 0; ε > 0 is a special case
--   - generalization: all registers d-dimensional qudits, and the resource prepared by a channel on |0^{2q}⟩ (§3.4) → any finite registers L, R, A₁, A₂, B₁, B₂ and any density matrix on LR, with Q, Q̄, Q₀, Q₁ of dimension d; reason: the statement needs only that they are finite; tuples of qudits and prepared resources are the special case
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 4.1, p.17

import Definitions.Def_FRouting_RoutingStrategy

set_option autoImplicit false

namespace FRouting

/-- **Theorem 4.1 (the universal fidelity gap).** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 4.1, p.17: "Let ε > 0. Consider an
f-routing strategy that is (1 − ε)-correct on an input (x, y), and assume f(x, y) = 1. Let
ρ_{Q̄AB} = (ρ^{xy})_{Q̄AB} be its mid-protocol state, and define F₀ := F(ρ_{Q̄A}, ρ_{Q̄} ⊗ ρ_A),
F₁ := F(ρ_{Q̄B}, ρ_{Q̄} ⊗ ρ_B). Then F₀ ≥ 1 − 4ε, F₁ ≤ 1/d + √(2ε)."

**Formalization Note** `0 ≤ ε` covers the printed `ε > 0`. `d ≥ 2` is Definition 3.6. -/
theorem theorem_4_1 {n d : ℕ} (hd : 2 ≤ d) (S : RoutingStrategy n d)
    (f : (Fin n → Bool) → (Fin n → Bool) → Bool) (ε : ℝ) (hε : 0 ≤ ε) (x y : Fin n → Bool)
    (hf : f x y = true) (hc : S.IsCorrectOn f ε x y) :
    1 - 4 * ε ≤ S.F0 x y ∧ S.F1 x y ≤ 1 / (d : ℝ) + Real.sqrt (2 * ε) := by sorry

end FRouting
