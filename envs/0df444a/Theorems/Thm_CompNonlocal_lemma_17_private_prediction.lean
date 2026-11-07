-- Prove2me | Theorems.Thm_CompNonlocal_lemma_17_private_prediction
-- name    : CompNonlocal.lemma_17_private_prediction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:54.316173+00:00
-- url     : https://prove2.me/theorems/4fcc3bb2-d021-4943-b959-e6995a309d29
-- title:
--   Lemma 17, p.44 — ASP gives a private prediction advantage $\ge\frac{\beta-\alpha}3-\frac1{q(\kappa)}$
-- statement:
--   Fix an $(\alpha,\beta)$-ASP. Run the preparation to get $(T,S,Q)$, pick $J$ uniformly in $\{1,2,3\}$, let $T^+=(T,J)$, let $B_R\in\{\pm1\}$ be the outcome of measuring $\sigma_J$ on $Q$, and $\hat B_S=(\hat r_S)_J$ with $\hat r_S$ the decoder's output. For every polynomial $q$ and every efficient public predictor $\mathcal A(T^+)\in[-1,1]$, eventually
--   $$\mathbb E\Big[(B_R-\mathcal A(T^+))^2-(B_R-\hat B_S)^2\Big]\ge\frac{\beta-\alpha}3-\frac1{q(\kappa)} .$$
--
--   This converts the ASP estimation gap into an advantage in predicting a private bit, the input of Lemma 18.
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - encoding: real and vector outputs r̂ ∈ ℝ³, predictions in [−1, 1], directions n ∈ S² → fixed dyadic decodings decDyadic, decVec, decDir; predictions clipped to [−1, 1]; reason: the paper fixes no bit format; decodable values are dense (Reading 5)
--   - generalization: (α, β)-ASP with α, β polynomial-time computable (Def 14) → IsASP without the computability of α, β; reason: the proof uses only 0 ≤ α < β ≤ 4 and β − α ≥ 1/p (Reading 8); every computable pair is an instance
--   - encoding: 1/q(κ) or 1/poly(κ) for a polynomial q → 1/(q(κ) + 1) with q ∈ ℕ[X]; reason: the same class of inverse-polynomial bounds, and no division by 0
--   - encoding: J ∈ {1, 2, 3} given to the predictor with T → J ∈ Fin 3 given as encNat J after msg_S ++ msg_R; reason: a fixed encoding of the challenge
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 17, p.44

import Mathlib
import Definitions.Def_CompNonlocal_IsASP
import Definitions.Def_CompNonlocal_ASP_predictionAdvantage

set_option autoImplicit false

namespace CompNonlocal

/-- **Lemma 17 (ASP gives a private prediction advantage).** Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), p.44: "Fix an (α, β)-ASP protocol, and use Prep and T⁺ as in Definition 15. For every
polynomial q and every efficient public predictor A(T⁺) ∈ [−1, 1], eventually
E[(B_R − A(T⁺))² − (B_R − B̂_S)² | (T, S, Q) ← Prep(1^κ), J ← {1, 2, 3}, T⁺ := (T, J), B_R ← outcome
of measuring σ_J on Q, r̂_S ← ASP.Dec(S, msg_S, msg_R), B̂_S := (r̂_S)_J] ≥ (β − α)/3 − 1/q(κ)."

**Formalization Note** An efficient public predictor is a polynomial-size family reading `T⁺`
(`ASP.predictionAdvantage`). "1/q(κ)" is `1/(q(κ) + 1)` for `q : Polynomial ℕ`; ranging over all such
`q` is the same as ranging over all positive polynomials. The order is `∀ q ∀ A`, eventually in `κ`. -/
theorem lemma_17_private_prediction (P : ASP) (α β : ℕ → ℝ) (hP : IsASP P α β)
    (q : Polynomial ℕ) (Pd : Family) (hPd : PolySize Pd) :
    ∀ᶠ κ in Filter.atTop,
      (β κ - α κ) / 3 - 1 / ((q.eval κ : ℕ) + 1 : ℝ) ≤ P.predictionAdvantage κ (Pd κ) := by sorry

end CompNonlocal
