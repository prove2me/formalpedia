-- Prove2me | Theorems.Thm_FRouting_lemma_4_2
-- name    : FRouting.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:06.600399+00:00
-- url     : https://prove2.me/theorems/82b18d10-1006-45e5-9bc6-f6664239aa06
-- title:
--   Lemma 4.2 — soundness separability
-- statement:
--   Let $d\ge2$ and $\varepsilon\ge0$. Consider a routing strategy that is $(1-\varepsilon)$-correct on an input $(x,y)$ with $f(x,y)=1$, and let $\rho=\rho^{xy}_{\bar QAB}$ be its mid-protocol state. Then
--   $$F_0=F(\rho_{\bar QA},\rho_{\bar Q}\otimes\rho_A)\ge1-4\varepsilon.$$
--
--   When Bob can recover the challenge, Alice's joint state with the reference is nearly a product.
--
--   Differences from the source:
--   - generalization: ε > 0 → 0 ≤ ε; reason: the proof works at ε = 0; ε > 0 is a special case
--   - generalization: all registers d-dimensional qudits, and the resource prepared by a channel on |0^{2q}⟩ (§3.4) → any finite registers L, R, A₁, A₂, B₁, B₂ and any density matrix on LR, with Q, Q̄, Q₀, Q₁ of dimension d; reason: the statement needs only that they are finite; tuples of qudits and prepared resources are the special case
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 4.2, p.17

import Definitions.Def_FRouting_RoutingStrategy

set_option autoImplicit false

namespace FRouting

/-- **Lemma 4.2 (soundness separability).** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 4.2, p.17: "Let ε > 0. Consider an f-routing
strategy that is (1 − ε)-correct on an input (x, y) satisfying f(x, y) = 1, and let ρ_{Q̄AB} = ρ^{xy}_{Q̄AB}
be its mid-protocol state. Then F₀ := F(ρ_{Q̄A}, ρ_{Q̄} ⊗ ρ_A) ≥ 1 − 4ε."

**Formalization Note** `0 ≤ ε` covers the printed `ε > 0`. `d ≥ 2` is Definition 3.6. -/
theorem lemma_4_2 {n d : ℕ} (hd : 2 ≤ d) (S : RoutingStrategy n d)
    (f : (Fin n → Bool) → (Fin n → Bool) → Bool) (ε : ℝ) (hε : 0 ≤ ε) (x y : Fin n → Bool)
    (hf : f x y = true) (hc : S.IsCorrectOn f ε x y) :
    1 - 4 * ε ≤ S.F0 x y := by sorry

end FRouting
