-- Prove2me | Theorems.Thm_FRouting_lemma_4_3
-- name    : FRouting.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:30.196876+00:00
-- url     : https://prove2.me/theorems/4742679c-f2e8-475f-b4e7-6b826cb0eaf1
-- title:
--   Lemma 4.3 — completeness inseparability
-- statement:
--   Let $d\ge2$. Consider a routing strategy that is $(1-\varepsilon)$-correct on an input $(x,y)$ with $f(x,y)=1$, and let $\rho=\rho^{xy}_{\bar QAB}$ be its mid-protocol state. Then
--   $$F_1=F(\rho_{\bar QB},\rho_{\bar Q}\otimes\rho_B)\le\frac1d+\sqrt{2\varepsilon}.$$
--
--   The intended recipient's joint state with the reference stays far from a product.
--
--   Differences from the source:
--   - generalization: all registers d-dimensional qudits, and the resource prepared by a channel on |0^{2q}⟩ (§3.4) → any finite registers L, R, A₁, A₂, B₁, B₂ and any density matrix on LR, with Q, Q̄, Q₀, Q₁ of dimension d; reason: the statement needs only that they are finite; tuples of qudits and prepared resources are the special case
--   - encoding: ε with no stated sign → 0 ≤ ε; reason: ε < 0 makes correctness ≥ 1 − ε unsatisfiable, and it would make √(2ε) a junk value
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 4.3, p.18

import Definitions.Def_FRouting_RoutingStrategy

set_option autoImplicit false

namespace FRouting

/-- **Lemma 4.3 (completeness inseparability).** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 4.3, p.18: "Consider an f-routing strategy
that is (1 − ε)-correct on an input (x, y) satisfying f(x, y) = 1, and let ρ_{Q̄AB} = (ρ^{xy})_{Q̄AB} be
its mid-protocol state. Then F₁ := F(ρ_{Q̄B}, ρ_{Q̄} ⊗ ρ_B) ≤ 1/d + √(2ε)."

**Formalization Note** `d ≥ 2` is Definition 3.6. `0 ≤ ε` keeps `√(2ε)` from being the junk value
of `Real.sqrt` on a negative number. -/
theorem lemma_4_3 {n d : ℕ} (hd : 2 ≤ d) (S : RoutingStrategy n d)
    (f : (Fin n → Bool) → (Fin n → Bool) → Bool) (ε : ℝ) (hε : 0 ≤ ε) (x y : Fin n → Bool)
    (hf : f x y = true) (hc : S.IsCorrectOn f ε x y) :
    S.F1 x y ≤ 1 / (d : ℝ) + Real.sqrt (2 * ε) := by sorry

end FRouting
