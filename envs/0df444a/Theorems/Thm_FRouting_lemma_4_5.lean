-- Prove2me | Theorems.Thm_FRouting_lemma_4_5
-- name    : FRouting.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:30.335836+00:00
-- url     : https://prove2.me/theorems/6f93fde9-36b8-4ad1-b5dd-63fcf7895507
-- title:
--   Lemma 4.5 — the EPR test on the product state
-- statement:
--   Under the hypotheses of Lemma 4.3, let $\omega_{\bar QQ_1}=(\mathrm{id}_{\bar Q}\otimes\mathcal V^{xy1}_{B\to Q_1})(\rho_{\bar Q}\otimes\rho_B)$. Then
--   $$\operatorname{tr}(\Phi\omega)=\frac1{d^2}.$$
--
--   Here $\rho_{\bar Q}$ is the marginal of the mid-protocol state; that it is maximally mixed is part of the content.
--
--   Differences from the source:
--   - generalization: all registers d-dimensional qudits, and the resource prepared by a channel on |0^{2q}⟩ (§3.4) → any finite registers L, R, A₁, A₂, B₁, B₂ and any density matrix on LR, with Q, Q̄, Q₀, Q₁ of dimension d; reason: the statement needs only that they are finite; tuples of qudits and prepared resources are the special case
--   - encoding: ε with no stated sign → 0 ≤ ε; reason: ε < 0 makes correctness ≥ 1 − ε unsatisfiable, and it would make √(2ε) a junk value
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 4.5, pp.19–20

import Definitions.Def_FRouting_RoutingStrategy
import Definitions.Def_WildeQIT_QMemory_idTensorChannel

set_option autoImplicit false

open scoped Kronecker

namespace FRouting

/-- **Lemma 4.5.** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 4.5, pp.19–20: "Under the hypotheses of Lemma 4.3, let
ω_{Q̄Q₁} := (id_{Q̄} ⊗ V^{xy1}_{B→Q₁})(ρ_{Q̄} ⊗ ρ_B). Then tr(Φω) = 1/d²."

**Formalization Note** `d ≥ 2` is Definition 3.6. The marginal `ρ_{Q̄}` is that of the mid-protocol
state: that it equals `I/d` is part of the content, never a hypothesis. -/
theorem lemma_4_5 {n d : ℕ} (hd : 2 ≤ d) (S : RoutingStrategy n d)
    (f : (Fin n → Bool) → (Fin n → Bool) → Bool) (ε : ℝ) (hε : 0 ≤ ε) (x y : Fin n → Bool)
    (hf : f x y = true) (hc : S.IsCorrectOn f ε x y) :
    (Phi d * WildeQIT.QMemory.idTensorChannel (S.Vₚ x y true)
        (margQ (S.midState x y) ⊗ₖ margB (S.midState x y))).trace = 1 / (d : ℂ) ^ 2 := by sorry

end FRouting
