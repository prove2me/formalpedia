-- Prove2me | Theorems.Thm_CompNonlocal_theorem_6_certification_implies_asp
-- name    : CompNonlocal.theorem_6_certification_implies_asp
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:50:18.327278+00:00
-- url     : https://prove2.me/theorems/3231db5e-7e2f-4248-8d1e-bf6805dc1396
-- title:
--   Theorem 6, p.34 — near-optimal Werner certification ($\delta=2^{-24}$) implies a $(1/450,3/16)$-ASP
-- statement:
--   Let $v\in(1/3,1]$ and suppose $\rho(v)$ is $\gamma$-single-copy certifiable with
--   $$\gamma\ge(1-\delta)\,\frac{v-\frac13}2,\qquad\delta:=2^{-24}. \tag{25}$$
--   Then there exists an $(\alpha,\beta)$-QCCC asymmetric state preparation with
--   $$\alpha=\frac1{450},\qquad\beta=\frac3{16},$$
--   in particular $\beta-\alpha=\Omega(1)$.
--
--   This is the cryptographic core of the paper: a near-optimal certificate yields a two-message protocol in which the sender estimates the receiver's prepared qubit much better than any efficient receiver can.
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - encoding: Val outputs a score w ∈ [0, 1] (Def 8) or v ∈ [−1, 1] ∪ {⊥} (Def 9); acceptance is the event v₁ < 0, a discarded round rejected (Def 11) → Val outputs one accept bit, its first output bit; reason: only the acceptance event is used for k = 1 (Reading 3)
--   - reading: every family of separable states {τ_AB} (Def 10) → every family of separable density matrices on C² ⊗ C², finite convex combinations of products; reason: the registers of the certified state (Reading 4); larger local spaces would strengthen the hypothesis; every two-qubit separable state is a finite convex combination
--   - encoding: real and vector outputs r̂ ∈ ℝ³, predictions in [−1, 1], directions n ∈ S² → fixed dyadic decodings decDyadic, decVec, decDir; predictions clipped to [−1, 1]; reason: the paper fixes no bit format; decodable values are dense (Reading 5)
--   - encoding: α, β polynomial-time computable (Def 14) → computability clause dropped from IsASP; reason: α = 1/450 and β = 3/16 are constants, trivially computable (Reading 8)
--   - encoding: 1/q(κ) or 1/poly(κ) for a polynomial q → 1/(q(κ) + 1) with q ∈ ℕ[X]; reason: the same class of inverse-polynomial bounds, and no division by 0
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 6, p.34, Eq. (25)

import Mathlib
import Definitions.Def_CompNonlocal_IsSingleCopyCertifiable
import Definitions.Def_CompNonlocal_IsASP
import Definitions.Def_CompNonlocal_werner

set_option autoImplicit false

namespace CompNonlocal

/-- **Theorem 6 (Near-optimal Werner state certification implies ASP).** Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), p.34: "Let v ∈ (1/3, 1] be fixed and suppose ρ(v) is γ-single-copy
certifiable with γ ≥ (1 − δ)(v − 1/3)/2, δ := 2^{−24}. (25) Then there exists an ASP with
β − α = Ω(1), and more concretely α = 1/450, β = 3/16."

**Formalization Note** The conclusion is an `(α, β)`-ASP with the constant functions `α = 1/450`,
`β = 3/16`, which gives `β − α = Ω(1)`. -/
theorem theorem_6_certification_implies_asp (v γ : ℝ) (hv₁ : 1 / 3 < v) (hv₂ : v ≤ 1)
    (hγ : (1 - (2 : ℝ) ^ (-24 : ℤ)) * ((v - 1 / 3) / 2) ≤ γ)
    (h : IsSingleCopyCertifiable (werner v) γ) :
    ∃ P : ASP, IsASP P (fun _ => 1 / 450) (fun _ => 3 / 16) := by sorry

end CompNonlocal
