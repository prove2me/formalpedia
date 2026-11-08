-- Prove2me | Theorems.Thm_FRouting_theorem_5_6
-- name    : FRouting.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:25.793971+00:00
-- url     : https://prove2.me/theorems/9c01b325-d785-410b-885d-67c305f9081a
-- title:
--   Theorem 5.6 — $\mathrm{coQSD}_{\alpha,\beta}\in\mathrm{QSZK}$ (Watrous)
-- statement:
--   For any constants $0\le\alpha<\beta^2\le1$ with $\beta\ge0$, there is a polynomial $B$ with
--   $$\mathrm{coQSD}_{\alpha,\beta}\in\mathrm{QSZK}(B).$$
--
--   The paper cites this from [Wat02; Wat09]. It is the external input of the goal.
--
--   Differences from the source:
--   - generalization: pairs of quantum circuits, read at d = 2 → instances over any qudit dimension d, verifier and simulator over qubit gates; reason: Lemma 5.7 feeds d-dimensional circuits to QSD; d = 2 is an instance, and the strict α < β² leaves room to synthesize F_d
--   - reading: "Quantum Statistical Zero-Knowledge proof", cited from [Wat02; Wat09] → InQSZK: qubit-circuit protocols, unrestricted provers, completeness ≥ 1 − μ, soundness ≤ μ, μ negligible and ≤ 1/3; reason: the paper does not define the proof; these errors imply both the 2/3–1/3 and the negligible conventions
--   - reading: "every verifier Ver* ... has a simulator" → cheating verifiers with auxiliary input, on the honest protocol's message qubits and number of rounds; the honest prover fixed first; trace distance tested on any finite reference; reason: the strong reading of [Wat09]; trivial auxiliary and reference recover the weaker one; a message the honest prover never reads, or a round it never answers, changes nothing
--   - reading: simulator time poly(T(n) + S(n)) → one polynomial r per problem, and a constant C per verifier: C · r(B + S); reason: a per-verifier polynomial would be weaker; a machine-dependent constant is unavoidable with exact step counts
--   - encoding: 0 ≤ α < β² ≤ 1 → the same, and 0 ≤ β; reason: Definition 5.5 has 0 ≤ α < β ≤ 1
--   - encoding: time at most B(n) for the honest and cheating verifiers → at most max(1, B(n)); reason: a machine takes at least one step; the bound changes only where B(n) = 0
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 5.6, p.21

import Definitions.Def_FRouting_InQSZK
import Definitions.Def_FRouting_QSD

set_option autoImplicit false

namespace FRouting

/-- **Theorem 5.6 (Watrous).** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 5.6, p.21: "For any constants 0 ≤ α < β² ≤ 1,
coQSD_{α,β} ∈ QSZK." Cited there from [Wat02; Wat09].

**Formalization Note** `QSZK` is the union over polynomial time bounds ("the usual class QSZK is
recovered by taking the union over polynomially bounded functions T", p.20). `0 ≤ β` is part of the
constants of Definition 5.5 (`0 ≤ α < β ≤ 1`); without it the promise is not one. The instances are
over any qudit dimension (see `QSDInstance`), and the verifier and the simulators are over the qubit
gates. At `d = 2` this is the printed theorem. -/
theorem theorem_5_6 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α < β ^ 2) (hβ1 : β ^ 2 ≤ 1) :
    ∃ B : Polynomial ℕ, InQSZK (coQSD α β) (fun m => B.eval m) := by sorry

end FRouting
