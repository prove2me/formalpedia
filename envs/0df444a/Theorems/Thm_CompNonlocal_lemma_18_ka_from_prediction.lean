-- Prove2me | Theorems.Thm_CompNonlocal_lemma_18_ka_from_prediction
-- name    : CompNonlocal.lemma_18_ka_from_prediction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:22.180046+00:00
-- url     : https://prove2.me/theorems/c60a3781-0909-489f-b13b-735f69647a16
-- title:
--   Lemma 18, p.45 — KA from private prediction
-- statement:
--   Suppose a sender-first two-message QCCC protocol (with uniform QPT parties) produces a transcript $Z$, a receiver bit $B_R\in\{-1,1\}$ and a sender value $\hat B_S\in[-1,1]$. If for some polynomial $q$ and every efficient public predictor $\mathcal A(Z)\in[-1,1]$, eventually
--   $$\mathbb E[(B_R-\mathcal A(Z))^2]\ge\mathbb E[(B_R-\hat B_S)^2]+\frac1{q(\kappa)},$$
--   then a sender-first two-message QCCC key agreement exists.
--
--   This is the general conversion of private prediction into key agreement (§9.2).
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - encoding: real and vector outputs r̂ ∈ ℝ³, predictions in [−1, 1], directions n ∈ S² → fixed dyadic decodings decDyadic, decVec, decDir; predictions clipped to [−1, 1]; reason: the paper fixes no bit format; decodable values are dense (Reading 5)
--   - encoding: 1/q(κ) or 1/poly(κ) for a polynomial q → 1/(q(κ) + 1) with q ∈ ℕ[X]; reason: the same class of inverse-polynomial bounds, and no division by 0
--   - encoding: answers, keys and messages are strings of the prescribed lengths → outputs read through fit n (first n bits, padded with 0); reason: a fixed local post-processing by the owner; it changes no party's power
--   - encoding: '≤ negl(κ)' for all sufficiently large κ → ∃ µ negligible, ∀ κ, … ≤ µ κ; reason: the quantities are bounded, so finitely many κ can be absorbed into µ; equivalent
--   - encoding: receiver bit B_R ∈ {−1, 1} → +1 when the receiver's private output starts with 1, −1 otherwise; reason: a fixed reading of the receiver's output
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 18, p.45

import Mathlib
import Definitions.Def_CompNonlocal_TwoMsg_PrivatePredictionAdvantage
import Definitions.Def_CompNonlocal_IsKA

set_option autoImplicit false

namespace CompNonlocal

/-- **Lemma 18 (KA from private prediction).** Głuch, Morimae, *From Computational Nonlocality to
Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), p.45:
"Suppose a sender-first two-message QCCC protocol produces a transcript Z, a receiver bit
B_R ∈ {−1, 1}, and a sender value B̂_S ∈ [−1, 1]. If, for some polynomial q and every efficient public
predictor A(Z) ∈ [−1, 1], eventually E[(B_R − A(Z))²] ≥ E[(B_R − B̂_S)²] + 1/q(κ), then a sender-first
two-message QCCC KA protocol exists."

**Formalization Note** The protocol's parties are uniform QPT ("All honest algorithms are uniform
QPT", p.18); the hypothesis is `TwoMsg.PrivatePredictionAdvantage`; the conclusion is a sender-first
two-message KA (`IsKA`, Definition 4). -/
theorem lemma_18_ka_from_prediction (P : TwoMsg) (h₁ : Uniform P.Sen1) (h₂ : Uniform P.Rec)
    (h₃ : Uniform P.Sen2) (hadv : P.PrivatePredictionAdvantage) :
    ∃ K : TwoMsg, IsKA K := by sorry

end CompNonlocal
