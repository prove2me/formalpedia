-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_C_7
-- name    : CondGeoVerif.Supplement.theorem_C_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:14:11.630003+00:00
-- url     : https://prove2.me/theorems/fe07b3e2-0b6c-444f-b1b9-bc6717237607
-- title:
--   Theorem C.7 (= Theorem 4.1) — the unknown Boolean family $\mathcal C_{K,d}$ at $\eta_K=2^{-3K}/(2^{14}K^4)$ with $m_V\le(2^{CK}/\varepsilon)\log(e/(\varepsilon\delta))$
-- statement:
--   For $K\ge1$, $\mathcal C_{K,d}$ is the class of all predictors $x\mapsto b(\mathrm{sign}(W^\top x))$ with an arbitrary Boolean rule $b$ and an orthonormal frame $W$ of rank at most $\min(K,d)$, constants included; features are $X\sim N(0,I_d)$.
--
--   There is a universal $C>0$ such that, for all integers $K,d\ge1$, $0<\varepsilon<1$ and $0<\delta\le1/4$, the class $\mathcal C_{K,d}$ has a proper one-message verifier at noise allowance
--   $$\eta_K=\frac{2^{-3K}}{2^{14}K^4}$$
--   with deterministic budgets
--   $$m_V\le\frac{2^{CK}}{\varepsilon}\log\frac e{\varepsilon\delta},\qquad m_P\le\frac{2^{CK}}{\varepsilon^2}\Big(d\log\frac e\varepsilon+\log\frac1\delta\Big).$$
--   Completeness permits full ambient Massart noise bounded by $\eta_K$; soundness permits arbitrary labels and compares against the entire union. Both the Boolean table and the orthonormal frame are unknown and supplied in the message. There is no runtime claim.
--
--   At fixed accuracy and confidence, growing rank $K=o(\log d)$ still gives $m_V=d^{o(1)}$.
--
--   Differences from the source:
--   - encoding: the message is a truth table and a frame → message type: a rank ℓ ≤ K, a truth table on {−1, 1}^ℓ and a d × ℓ matrix; every output is the composition the message names, with an orthonormal frame; reason: the paper's message, made a type
--   - encoding: 2^{CK} → the real power (2:ℝ)^(C·K); reason: C is real
--   - encoding: labels in {−1, 1}; a sign on a zero hyperplane can be chosen arbitrarily → labels Bool (true ↔ +1), sign(0) = +1; reason: hyperplanes are Gaussian-null, so no probability in the statement depends on the convention (App. C, p.28)
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem C.7, pp.32–33 (PDF pp.35–36); identical to Theorem 4.1, p.8 (PDF p.11)

import Mathlib
import Definitions.Def_CondGeoVerif_Supplement_boolComp

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem C.7 (Quantitative verification of the unknown Boolean family)** (Chen, *The
Conditional Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…,
pp.32–33 = PDF pp.35–36; identical to Theorem 4.1, p.8). There is a universal `C > 0` such that,
for all integers `K, d ≥ 1`, `0 < ε < 1` and `0 < δ ≤ 1/4`, the class `C_{K,d}` has a proper
one-message verifier at noise allowance `η_K = 2^{−3K}/(2^{14}K⁴)` with deterministic budgets
`m_V ≤ (2^{CK}/ε) log(e/(εδ))` and `m_P ≤ (2^{CK}/ε²)(d log(e/ε) + log(1/δ))`. Completeness permits
full ambient Massart noise; soundness permits arbitrary labels and compares against the entire union.
Both the Boolean table and the orthonormal frame are unknown and supplied in the message.

**Formalization Note** The message type is `BoolFrameMsg K d` (a rank `ℓ ≤ K`, a truth table on
`{−1, 1}^ℓ` and a `d × ℓ` matrix); `OutputsBoolFrame` says every output is the composition the
message names, with an orthonormal frame. `C` is chosen before `K, d, ε, δ`. No runtime claim. -/
theorem theorem_C_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ K d : ℕ, 1 ≤ K → 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ (V : OneMsgVerifier d (BoolFrameMsg K d)) (Hon : HonestProver d (BoolFrameMsg K d)),
          ProperInClass V (boolClass K d) ∧ OutputsBoolFrame V ∧
          OMSound V (boolClass K d) ε δ ∧
          OMMassartComplete V Hon (boolClass K d)
            ((2 : ℝ) ^ (-(3 * (K : ℤ))) / (2 ^ 14 * (K : ℝ) ^ 4)) ε δ ∧
          (V.m : ℝ) ≤ (2 : ℝ) ^ (C * K) / ε * Real.log (Real.exp 1 / (ε * δ)) ∧
          (Hon.mP : ℝ) ≤ (2 : ℝ) ^ (C * K) / ε ^ 2 *
            (d * Real.log (Real.exp 1 / ε) + Real.log (1 / δ)) := by sorry

end CondGeoVerif.Supplement
