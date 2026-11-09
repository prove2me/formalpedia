-- Prove2me | Theorems.Thm_CondGeoVerif_theorem_A_1
-- name    : CondGeoVerif.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:32:58.89345+00:00
-- url     : https://prove2.me/theorems/98695b61-738f-4de9-a1cd-2aaf6b4a3651
-- title:
--   Theorem A.1 — fixed-rule upper bounds $O(\log\frac1\delta)$, $O(\sqrt d\log\frac1\delta)$, $O(d+\log\frac1\delta)$
-- statement:
--   For every fixed Borel rule $f:\mathbb R^k\to\{-1,1\}$, $k\ge1$, every $0<\eta<1/2$ and every fixed $0<\varepsilon<1$, there are proper one-message verifiers for $\mathcal H_{f,d}$ with full Massart completeness and arbitrary-label Gaussian soundness such that, for all $d\ge k$ and $0<\delta\le1/4$:
--   1. if $J_0(A;\eta)\le0$ for every contraction $A$, the private sample count is $O_{f,k,\eta,\varepsilon}(\log(1/\delta))$;
--   2. if $J_1(A;\eta)\le0$ for every contraction $A$, it is $O_{f,k,\eta,\varepsilon}(\sqrt d\log(1/\delta))$;
--   3. without either condition, it is $O_{f,k,\eta,\varepsilon}(d+\log(1/\delta))$.
--
--   In all three cases an honest independent sample-only prover needs $O_{f,k,\eta,\varepsilon}(d+\log(1/\delta))$ observations. The second protocol's message contains at most $k+O_k(\varepsilon^{-2})$ orthonormal directions.
--
--   These are the fixed-rule upper bounds of the dimension classification.
--
--   Differences from the source:
--   - generalization: soundness for every prover strategy → soundness for every fixed message, of any type and with no measurability in the message; reason: a random message sent before the private sample is a mixture of fixed messages, and a malicious prover may know the law; the printed requirement follows
--   - reading: one-message protocols whose probabilities "include the samples and all protocol randomness" → for each message the acceptance bit is measurable in (sample, coins) and the output predictor jointly measurable in (sample, coins, feature); the honest run is jointly measurable in (prover sample, prover coins, verifier sample, verifier coins); reason: the probabilities of Definition 2.1 are defined only for measurable protocols, and improper outputs are 'measurable Boolean predictors'
--   - encoding: O(·) bounds with constants depending on the fixed parameters; Massart noise P(Y ≠ h*(X) | X) ≤ η a.s. → ∃ C chosen after the fixed parameters and before d, δ; Massart as P({X ∈ B, Y ≠ h*(X)}) ≤ η·N(0,I_d)(B) for Borel B; reason: Lean convention; equivalent statements
--   - encoding: "the second protocol's message contains at most k + O_k(ε⁻²) orthonormal directions" → the message type is a frame with at most N ≤ k + C_k/ε² columns, C_k chosen after k only, and the verifier outputs only on orthonormal frames; reason: Lean convention for the message size
--   - encoding: labels and rule values in {−1, 1} → Bool, with true for +1; reason: Lean convention; the same instances
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem A.1, pp.13–14 (PDF pp.16–17)

import Mathlib
import Definitions.Def_CondGeoVerif_Jprog
import Definitions.Def_CondGeoVerif_OneMsgVerifier

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **Theorem A.1 (Conditional-moment classification), upper bounds** (Chen, *The Conditional
Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, pp.13–14 =
PDF pp.16–17). For every fixed Borel rule `f : ℝᵏ → {−1, 1}`, `0 < η < 1/2`, every fixed
`0 < ε < 1`, every `d ≥ k` and `0 < δ ≤ 1/4`, there are proper one-message verifiers for
`H_{f,d}` with full Massart completeness and arbitrary-label Gaussian soundness such that:
1. if `J₀(A; η) ≤ 0` for every contraction `A`, the private sample count is `O_{f,k,η,ε}(log(1/δ))`;
2. if `J₁(A; η) ≤ 0` for every contraction `A`, it is `O_{f,k,η,ε}(√d log(1/δ))`;
3. without either condition, it is `O_{f,k,η,ε}(d + log(1/δ))`.
In all three cases an honest independent sample-only prover needs `O_{f,k,η,ε}(d + log(1/δ))`
observations. The second protocol's message contains at most `k + O_k(ε⁻²)` orthonormal
directions.

**Formalization Note** `J_j(A; η) = J_j(f, f, A; η)`. Each `O(·)` is a constant `C` chosen after
`f, η, ε` and before `d, δ`; the `O_k(ε⁻²)` constant `C_k` is chosen after `k` and before `f, η, ε`.
Each row has its own verifier and honest prover; the honest prover is fixed before the law. In
row 2 the message is a frame with at most `N ≤ k + C_k/ε²` columns, and the verifier rejects every
message whose frame is not orthonormal. -/
theorem theorem_A_1 {k : ℕ} (hk : 1 ≤ k) :
    ∃ Ck : ℝ, ∀ f : Vec k → Bool, Measurable f → ∀ η : ℝ, 0 < η → η < 1 / 2 →
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ((∀ A : Matrix (Fin k) (Fin k) ℝ, IsContraction A → Jprog 0 f f A η ≤ 0) →
        ∃ C : ℝ, ∀ d : ℕ, k ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
          ∃ (Msg : Type) (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg),
            ProperIn V ({f} : Set (Vec k → Bool)) ∧ OMSound V (projClass {f} d) ε δ ∧
            OMMassartComplete V Hon (projClass {f} d) η ε δ ∧
            (V.m : ℝ) ≤ C * Real.log (1 / δ) ∧ (Hon.mP : ℝ) ≤ C * (d + Real.log (1 / δ))) ∧
      ((∀ A : Matrix (Fin k) (Fin k) ℝ, IsContraction A → Jprog 1 f f A η ≤ 0) →
        ∃ (C : ℝ) (N : ℕ), (N : ℝ) ≤ k + Ck / ε ^ 2 ∧
          ∀ d : ℕ, k ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∃ (V : OneMsgVerifier d (FrameMsg d N)) (Hon : HonestProver d (FrameMsg d N)),
              ProperIn V ({f} : Set (Vec k → Bool)) ∧ ChecksFrame V id ∧
              OMSound V (projClass {f} d) ε δ ∧ OMMassartComplete V Hon (projClass {f} d) η ε δ ∧
              (V.m : ℝ) ≤ C * Real.sqrt d * Real.log (1 / δ) ∧
              (Hon.mP : ℝ) ≤ C * (d + Real.log (1 / δ))) ∧
      (∃ C : ℝ, ∀ d : ℕ, k ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ (Msg : Type) (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg),
          ProperIn V ({f} : Set (Vec k → Bool)) ∧ OMSound V (projClass {f} d) ε δ ∧
          OMMassartComplete V Hon (projClass {f} d) η ε δ ∧
          (V.m : ℝ) ≤ C * (d + Real.log (1 / δ)) ∧ (Hon.mP : ℝ) ≤ C * (d + Real.log (1 / δ))) := by sorry

end CondGeoVerif
