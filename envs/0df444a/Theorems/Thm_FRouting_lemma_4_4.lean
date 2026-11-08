-- Prove2me | Theorems.Thm_FRouting_lemma_4_4
-- name    : FRouting.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:21.605339+00:00
-- url     : https://prove2.me/theorems/ef3b3e7d-c512-4d9b-8cda-4705770a9a9b
-- title:
--   Lemma 4.4 — the EPR test on the decoded state
-- statement:
--   Under the hypotheses of Lemma 4.3, let $\sigma_{\bar QQ_1}=(\mathrm{id}_{\bar Q}\otimes\mathcal V^{xy1}_{B\to Q_1})(\rho_{\bar QB})$. Then
--   $$\operatorname{tr}(\Phi\sigma)\ge1-2\varepsilon.$$
--
--   Differences from the source:
--   - generalization: all registers d-dimensional qudits, and the resource prepared by a channel on |0^{2q}⟩ (§3.4) → any finite registers L, R, A₁, A₂, B₁, B₂ and any density matrix on LR, with Q, Q̄, Q₀, Q₁ of dimension d; reason: the statement needs only that they are finite; tuples of qudits and prepared resources are the special case
--   - encoding: ε with no stated sign → 0 ≤ ε; reason: ε < 0 makes correctness ≥ 1 − ε unsatisfiable, and it would make √(2ε) a junk value
--   - encoding: tr(Φσ), a real number → the real part of tr(Φσ); reason: Φ and σ are positive semidefinite, so the trace is real
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 4.4, p.19

import Definitions.Def_FRouting_RoutingStrategy
import Definitions.Def_WildeQIT_QMemory_idTensorChannel

set_option autoImplicit false

namespace FRouting

/-- **Lemma 4.4.** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Lemma 4.4, p.19: "Under the hypotheses of Lemma 4.3, let
σ_{Q̄Q₁} := (id_{Q̄} ⊗ V^{xy1}_{B→Q₁})(ρ_{Q̄B}). Then tr(Φσ) ≥ 1 − 2ε."

**Formalization Note** `d ≥ 2` is Definition 3.6. The trace is real, since `Φ` and `σ` are positive
semidefinite; its real part is taken to state the inequality. -/
theorem lemma_4_4 {n d : ℕ} (hd : 2 ≤ d) (S : RoutingStrategy n d)
    (f : (Fin n → Bool) → (Fin n → Bool) → Bool) (ε : ℝ) (hε : 0 ≤ ε) (x y : Fin n → Bool)
    (hf : f x y = true) (hc : S.IsCorrectOn f ε x y) :
    1 - 2 * ε ≤
      (Phi d * WildeQIT.QMemory.idTensorChannel (S.Vₚ x y true) (margQB (S.midState x y))).trace.re := by sorry

end FRouting
