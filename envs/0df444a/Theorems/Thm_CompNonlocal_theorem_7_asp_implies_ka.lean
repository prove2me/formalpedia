-- Prove2me | Theorems.Thm_CompNonlocal_theorem_7_asp_implies_ka
-- name    : CompNonlocal.theorem_7_asp_implies_ka
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:46.773311+00:00
-- url     : https://prove2.me/theorems/23d75476-2432-4cff-b0d5-f949bcf4cdf1
-- title:
--   Theorem 7, p.44 — ASP implies sender-first two-message QCCC KA
-- statement:
--   Every $(\alpha,\beta)$-QCCC asymmetric state preparation implies a sender-first two-message QCCC key agreement (Definition 4): there are uniform QPT $\mathrm{Sen}_1,\mathrm{Rec},\mathrm{Sen}_2$ with keys in $\{0,1\}^\kappa$ that agree except with negligible probability and are computationally indistinguishable from uniform given the complete transcript.
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - generalization: (α, β)-ASP with α, β polynomial-time computable (Def 14) → IsASP without the computability of α, β; reason: the proof uses only 0 ≤ α < β ≤ 4 and β − α ≥ 1/p (Reading 8); every computable pair is an instance
--   - encoding: answers, keys and messages are strings of the prescribed lengths → outputs read through fit n (first n bits, padded with 0); reason: a fixed local post-processing by the owner; it changes no party's power
--   - encoding: '≤ negl(κ)' for all sufficiently large κ → ∃ µ negligible, ∀ κ, … ≤ µ κ; reason: the quantities are bounded, so finitely many κ can be absorbed into µ; equivalent
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 7, p.44

import Mathlib
import Definitions.Def_CompNonlocal_IsASP
import Definitions.Def_CompNonlocal_IsKA

set_option autoImplicit false

namespace CompNonlocal

/-- **Theorem 7 (ASP implies KA).** Głuch, Morimae, *From Computational Nonlocality to Public-Key
Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), p.44: "ASP implies
a sender-first two-message QCCC KA protocol (Definition 4)."

**Formalization Note** For every `(α, β)`-ASP (Definition 14 without the polynomial-time
computability of `α, β`, Reading 8) there is a sender-first two-message KA (`IsKA`). -/
theorem theorem_7_asp_implies_ka (P : ASP) (α β : ℕ → ℝ) (hP : IsASP P α β) :
    ∃ K : TwoMsg, IsKA K := by sorry

end CompNonlocal
