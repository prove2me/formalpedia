-- Prove2me | Theorems.Thm_CompNonlocal_lemma_19_log_loss
-- name    : CompNonlocal.lemma_19_log_loss
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:06.16367+00:00
-- url     : https://prove2.me/theorems/79fe882a-b836-4ae7-9e9b-8f83b1dccae7
-- title:
--   Lemma 19, p.45 — from quadratic to logarithmic loss
-- statement:
--   A sender-first two-message protocol satisfying the hypothesis of Lemma 18 can be modified by local postprocessing to a protocol $\Pi$ in which the receiver outputs a bit $B\in\{0,1\}$ and the sender a value $p\in[1/4,3/4]$ (its predicted probability that $B=1$). There is a polynomial $q$ such that every efficient public bit sampler $S$ eventually satisfies
--   $$\mathbb E\left[\log_2\frac{p^b(1-p)^{1-b}}{\Pr[S(z)=b]}\ \middle|\ (z,b,p)\leftarrow\Pi(1^\kappa)\right]\ge\frac1{q(\kappa)},$$
--   where $z$ is the public transcript: the sampler's logarithmic loss exceeds the sender's by an inverse polynomial.
--
--   The entropy tools of §9.2 work with logarithmic loss; this lemma supplies the entropy gap they need.
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - encoding: real and vector outputs r̂ ∈ ℝ³, predictions in [−1, 1], directions n ∈ S² → fixed dyadic decodings decDyadic, decVec, decDir; predictions clipped to [−1, 1]; reason: the paper fixes no bit format; decodable values are dense (Reading 5)
--   - encoding: 1/q(κ) or 1/poly(κ) for a polynomial q → 1/(q(κ) + 1) with q ∈ ℕ[X]; reason: the same class of inverse-polynomial bounds, and no division by 0
--   - encoding: log loss −log Pr[S(z) = b] = +∞ when Pr[S(z) = b] = 0 → disjunction: either such an outcome has positive probability, or the real expectation is ≥ 1/(q + 1); reason: Real.logb 0 = 0 in Lean; an infinite loss satisfies the bound (Reading 7)
--   - encoding: 'modified by local postprocessing'; receiver bit B, sender value p → TwoMsg.IsLocalPostprocessing (law of Π = law of P with each party's output passed through a finite-support kernel); B the first bit of Π's receiver output, p its sender output read by decDyadic, almost surely in [1/4, 3/4]; reason: the same transcript and local, independent output transformations
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 19, p.45 and footnote 8

import Mathlib
import Definitions.Def_CompNonlocal_TwoMsg_PrivatePredictionAdvantage
import Definitions.Def_CompNonlocal_TwoMsg_IsLocalPostprocessing
import Definitions.Def_CompNonlocal_Uniform

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- **Lemma 19 (From quadratic to logarithmic loss).** Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), p.45: "A protocol satisfying the hypothesis of Lemma 18 can be modified by local
postprocessing to obtain a protocol Π in which the receiver outputs a bit B ∈ {0, 1} and the sender a
value p ∈ [1/4, 3/4]. There exists a polynomial q such that every efficient public bit sampler S
eventually satisfies E[log₂(p^b(1 − p)^{1−b} / Pr[S(z) = b]) | (z, b, p) ← Π(1^κ)] ≥ 1/q(κ). Here
Π(1^κ) denotes an honest execution returning the public transcript z, the receiver's bit b, and the
sender's value p; Z denotes the random transcript. The log ratio is the public sampler's logarithmic
loss minus the sender's." Footnote 8: "Interpret p as the sender's predicted probability that B = 1."

**Formalization Note** The hypothesis of Lemma 18: a sender-first two-message protocol with uniform
QPT parties and `TwoMsg.PrivatePredictionAdvantage`. In `Π` (here `Q`), the receiver's bit is the
first bit of its private output (`true` = 1) and the sender's value `p` is its output read by
`decDyadic`, almost surely in `[1/4, 3/4]`. A public bit sampler is a polynomial-size family reading
`z = msg_S ++ msg_R`; `Pr[S(z) = b]` is the probability that its first output bit is `b`. When this
probability is `0` on an outcome of positive probability, the sampler's loss is `+∞` and the bound
holds; that case is the first disjunct (Lean's `Real.logb` of `0` would be `0`). -/
theorem lemma_19_log_loss (P : TwoMsg) (h₁ : Uniform P.Sen1) (h₂ : Uniform P.Rec)
    (h₃ : Uniform P.Sen2) (hadv : P.PrivatePredictionAdvantage) :
    ∃ Q : TwoMsg, Uniform Q.Sen1 ∧ Uniform Q.Rec ∧ Uniform Q.Sen2 ∧ P.IsLocalPostprocessing Q ∧
      (∀ κ, Q.expect κ (fun _ _ _ oS =>
          if 1 / 4 ≤ (decDyadic oS).1 ∧ (decDyadic oS).1 ≤ 3 / 4 then 0 else 1) = 0) ∧
      ∃ q : Polynomial ℕ, ∀ S : Family, PolySize S → ∀ᶠ κ in Filter.atTop,
        0 < Q.expect κ (fun mS mR oR _ =>
            if ((S κ).effectOn 0 (mS ++ mR)
                (fun t => decide (t.headD false = oR.headD false))).trace.re = 0 then 1 else 0) ∨
        1 / ((q.eval κ : ℕ) + 1 : ℝ) ≤
          Q.expect κ (fun mS mR oR oS =>
            Real.logb 2 (if oR.headD false then (decDyadic oS).1 else 1 - (decDyadic oS).1) -
              Real.logb 2 ((S κ).effectOn 0 (mS ++ mR)
                (fun t => decide (t.headD false = oR.headD false))).trace.re) := by sorry

end CompNonlocal
