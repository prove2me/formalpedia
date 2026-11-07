-- Prove2me | Theorems.Thm_CompNonlocal_near_optimal_certification_implies_ka_and_pke
-- name    : CompNonlocal.near_optimal_certification_implies_ka_and_pke
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:47.53606+00:00
-- url     : https://prove2.me/theorems/d73ec847-1461-4e8e-b8c3-532d4c1d3858
-- title:
--   Theorem 1 (formal form: Theorems 6, 7 and Corollary 3), p.5 — near-optimal certification of $\rho(v)$ gives two-message KA and PKE
-- statement:
--   Call a one-round single-copy certificate for the Werner state $\rho(v)$, $v>1/3$, **$\delta$-optimal** if its gap satisfies
--   $$\gamma\ge(1-\delta)\,\frac{v-\frac13}2 . \tag{1}$$
--   **Theorem 1.** For $\delta=2^{-24}$: if $v\in(1/3,1]$ and $\rho(v)$ is $\gamma$-single-copy certifiable with $\gamma$ as in (1), then
--
--   1. there is a sender-first two-message QCCC key agreement (Definition 4), and
--   2. there is a QCCC public-key encryption scheme (Definition 5): CPA-secure, with classical public keys and ciphertexts, and a possibly quantum secret key supporting polynomially many successive decryptions of fresh honestly generated ciphertexts.
--
--   The paper states Theorem 1 informally ("for sufficiently small constant $\delta$"); its proof is Theorem 6 (certification $\Rightarrow$ ASP with $\delta=2^{-24}$), Theorem 7 (ASP $\Rightarrow$ KA) and Corollary 3 (ASP $\Rightarrow$ PKE). The result reduces public-key cryptography in the QCCC model to a quantitative question about computational nonlocality of a single entangled two-qubit state.
--
--   Differences from the source:
--   - reading: 'for sufficiently small constant δ' (informal Theorem 1) → δ = 2^{−24}, the value fixed by Theorem 6 (Eq. (25)); reason: Reading 1; it implies the informal statement for every δ ≤ 2^{−24}
--   - reading: 'two-message QCCC KA' → a sender-first two-message KA (TwoMsg, IsKA); reason: the form Theorem 7 gives and the p.6 conversion uses
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - encoding: Val outputs a score w ∈ [0, 1] (Def 8) or v ∈ [−1, 1] ∪ {⊥} (Def 9); acceptance is the event v₁ < 0, a discarded round rejected (Def 11) → Val outputs one accept bit, its first output bit; reason: only the acceptance event is used for k = 1 (Reading 3)
--   - reading: every family of separable states {τ_AB} (Def 10) → every family of separable density matrices on C² ⊗ C², finite convex combinations of products; reason: the registers of the certified state (Reading 4); larger local spaces would strengthen the hypothesis; every two-qubit separable state is a finite convex combination
--   - encoding: answers, keys and messages are strings of the prescribed lengths → outputs read through fit n (first n bits, padded with 0); reason: a fixed local post-processing by the owner; it changes no party's power
--   - encoding: '≤ negl(κ)' for all sufficiently large κ → ∃ µ negligible, ∀ κ, … ≤ µ κ; reason: the quantities are bounded, so finitely many κ can be absorbed into µ; equivalent
--   - reading: PKE correctness and reuse 'negligible' per message / message sequence → one negligible bound for all messages and all adaptive choosers; reason: the stronger reading (Reading 6), equivalent since at each κ finitely many behaviours matter
--   - encoding: γ(κ) > 1/poly(κ) for all sufficiently large κ (Def 10) → ∃ q ∈ ℕ[X], eventually 1/(q(κ) + 1) < c(κ) − s(κ) (inside IsCertificateFor); reason: the same class of inverse-polynomial bounds, and no division by 0
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 1, p.5 (formal form: Theorem 6, p.34; Theorem 7, p.44; Corollary 3, p.52)

import Mathlib
import Definitions.Def_CompNonlocal_IsSingleCopyCertifiable
import Definitions.Def_CompNonlocal_IsKA
import Definitions.Def_CompNonlocal_IsPKE
import Definitions.Def_CompNonlocal_werner

set_option autoImplicit false

namespace CompNonlocal

/-- **Theorem 1 (formal form: Theorems 6, 7 and Corollary 3).** Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), p.5: "For a fixed v > 1/3, we call a one-round, single-copy certificate for ρ(v) δ-optimal
if its gap satisfies γ ≥ (1 − δ)(v − 1/3)/2. (1) Theorem 1 (Informal). For sufficiently small constant
δ, δ-optimal certification of an entangled Werner state implies two-message QCCC KA and PKE. The
encryption scheme is CPA-secure, with classical public keys and ciphertexts. Its secret key may be
quantum and supports polynomially many successive decryptions of fresh honestly generated
ciphertexts." p.6: "The standard conversion from two-message KA to PKE [BDK+11, Section 4.3], adapted
to quantum secret keys in Corollary 3, gives Theorem 1."

**Formalization Note** The informal Theorem 1 in the form its proof gives (Theorem 6, p.34,
Theorem 7, p.44, Corollary 3, p.52): with `δ = 2^{−24}` (Eq. (25); Reading 1), for every entangled
Werner state `ρ(v)`, `v ∈ (1/3, 1]`, γ-single-copy certifiability with `γ ≥ (1 − δ)(v − 1/3)/2`
gives a sender-first two-message QCCC KA and a QCCC PKE (Definitions 4, 5). -/
theorem near_optimal_certification_implies_ka_and_pke (v : ℝ) (hv₁ : 1 / 3 < v) (hv₂ : v ≤ 1)
    (γ : ℝ) (hγ : (1 - (2 : ℝ) ^ (-24 : ℤ)) * ((v - 1 / 3) / 2) ≤ γ)
    (h : IsSingleCopyCertifiable (werner v) γ) :
    (∃ P : TwoMsg, IsKA P) ∧ (∃ E : PKE, IsPKE E) := by sorry

end CompNonlocal
