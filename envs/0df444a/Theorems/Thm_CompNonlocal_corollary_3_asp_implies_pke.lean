-- Prove2me | Theorems.Thm_CompNonlocal_corollary_3_asp_implies_pke
-- name    : CompNonlocal.corollary_3_asp_implies_pke
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:42.477257+00:00
-- url     : https://prove2.me/theorems/2afe2272-b853-40d2-94cd-6a78e7eeae96
-- title:
--   Corollary 3, p.52 — ASP implies QCCC PKE with key reuse
-- statement:
--   Every $(\alpha,\beta)$-QCCC asymmetric state preparation implies a QCCC public-key encryption scheme (Definition 5) with classical public keys and ciphertexts and a possibly quantum secret key supporting polynomially many successive decryptions of honestly generated ciphertexts, which is IND-CPA secure against polynomial-size adversaries keeping quantum memory between the two stages.
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - generalization: (α, β)-ASP with α, β polynomial-time computable (Def 14) → IsASP without the computability of α, β; reason: the proof uses only 0 ≤ α < β ≤ 4 and β − α ≥ 1/p (Reading 8); every computable pair is an instance
--   - encoding: answers, keys and messages are strings of the prescribed lengths → outputs read through fit n (first n bits, padded with 0); reason: a fixed local post-processing by the owner; it changes no party's power
--   - encoding: '≤ negl(κ)' for all sufficiently large κ → ∃ µ negligible, ∀ κ, … ≤ µ κ; reason: the quantities are bounded, so finitely many κ can be absorbed into µ; equivalent
--   - reading: 'for every m, Pr[m′ = m] ≥ 1 − negl'; 'the probability that any m′_i ≠ m_i is negligible' for adaptive messages → one negligible bound for all messages, resp. for all adaptive message choosers (functions of pk and the previous ciphertexts); reason: the stronger reading (Reading 6); equivalent, since at each κ finitely many behaviours matter
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Corollary 3, p.52

import Mathlib
import Definitions.Def_CompNonlocal_IsASP
import Definitions.Def_CompNonlocal_IsPKE

set_option autoImplicit false

namespace CompNonlocal

/-- **Corollary 3 (ASP implies PKE).** Głuch, Morimae, *From Computational Nonlocality to Public-Key
Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), p.52: "ASP implies
QCCC PKE (Definition 5) with classical public keys and ciphertexts and a possibly quantum secret key
supporting polynomially many successive decryptions of honestly generated ciphertexts."

**Formalization Note** Classical public keys and ciphertexts and a retained quantum secret key are the
syntax of `PKE`; "polynomially many successive decryptions" is the reuse clause of `IsPKE`. The ASP
hypothesis omits the computability of `α, β` (Reading 8). -/
theorem corollary_3_asp_implies_pke (P : ASP) (α β : ℕ → ℝ) (hP : IsASP P α β) :
    ∃ E : PKE, IsPKE E := by sorry

end CompNonlocal
