-- Prove2me | Theorems.Thm_CondGeoVerif_theorem_A_5_upper
-- name    : CondGeoVerif.theorem_A_5_upper
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:36:16.145206+00:00
-- url     : https://prove2.me/theorems/4d67bbcd-cc04-4b97-b070-02a8ede8dfdb
-- title:
--   Theorem A.5 (upper part) — family upper bounds with a finite rule alphabet
-- statement:
--   Let $F$ be a nonempty family of Borel rules $\mathbb R^K\to\{-1,1\}$, $K\ge1$, totally bounded in Gaussian disagreement, $0<\eta<1/2$ and $0<\varepsilon<1$. The three upper bounds and honest-prover budgets of Theorem A.1 hold for $\mathcal H_{F,d}$, with constants depending on $F,K,\eta,\varepsilon$, when each envelope condition is imposed on every ordered triple $(f,g,A)$: for all $d\ge K$ and $0<\delta\le1/4$, the private sample count is $O(\log(1/\delta))$ if $J_0(f,g,A;\eta)\le0$ everywhere, $O(\sqrt d\log(1/\delta))$ if $J_1(f,g,A;\eta)\le0$ everywhere, and $O(d+\log(1/\delta))$ in general, and the honest sample-only prover uses $O(d+\log(1/\delta))$ observations. The protocols are proper, use one message, have full Massart completeness and arbitrary-label Gaussian soundness against the entire union, and name a rule from a fixed finite subset of $F$. The square-root protocol reveals at most $K+O_K(\varepsilon^{-2})$ orthonormal directions.
--
--   Differences from the source:
--   - generalization: soundness for every prover strategy → soundness for every fixed message, of any type and with no measurability in the message; reason: a random message sent before the private sample is a mixture of fixed messages, and a malicious prover may know the law; the printed requirement follows
--   - reading: one-message protocols whose probabilities "include the samples and all protocol randomness" → for each message the acceptance bit is measurable in (sample, coins) and the output predictor jointly measurable in (sample, coins, feature); the honest run is jointly measurable in (prover sample, prover coins, verifier sample, verifier coins); reason: the probabilities of Definition 2.1 are defined only for measurable protocols, and improper outputs are 'measurable Boolean predictors'
--   - encoding: O(·) bounds with constants depending on the fixed parameters; Massart noise P(Y ≠ h*(X) | X) ≤ η a.s. → ∃ C chosen after the fixed parameters and before d, δ; Massart as P({X ∈ B, Y ≠ h*(X)}) ≤ η·N(0,I_d)(B) for Borel B; reason: Lean convention; equivalent statements
--   - encoding: "name a rule from a fixed finite subset of F"; "reveals at most K + O_K(ε⁻²) orthonormal directions" → outputs use rules from a Finset F₀ ⊆ F chosen before d, δ; the square-root message is a rule with a frame of at most N ≤ K + C_K/ε² columns, C_K chosen after K only, and the verifier outputs only on orthonormal frames; reason: Lean convention for the alphabet and the message size
--   - encoding: labels and rule values in {−1, 1} → Bool, with true for +1; reason: Lean convention; the same instances
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem A.5, p.21 (PDF p.24), first paragraph

import Mathlib
import Definitions.Def_CondGeoVerif_Jprog
import Definitions.Def_CondGeoVerif_GaussTotallyBounded
import Definitions.Def_CondGeoVerif_OneMsgVerifier

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **Theorem A.5 (Unknown-rule family classification), upper part** (Chen, *The Conditional
Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, p.21 =
PDF p.24). Let `F` be a nonempty family of Borel rules `ℝᴷ → {−1, 1}`, totally bounded in Gaussian
disagreement, `0 < η < 1/2`, `0 < ε < 1`. The three upper bounds and honest-prover budgets of
Theorem A.1 hold for `H_{F,d}`, with constants depending on `F, K, η, ε`, when each envelope
condition is imposed on every ordered triple `(f, g, A)`: `O(log(1/δ))` if `J₀(f, g, A; η) ≤ 0`
everywhere, `O(√d log(1/δ))` if `J₁(f, g, A; η) ≤ 0` everywhere, `O(d + log(1/δ))` in general, and
`O(d + log(1/δ))` honest-prover observations in each case, for `d ≥ K`, `0 < δ ≤ 1/4`. The
protocols are proper, use one message, have full Massart completeness and arbitrary-label Gaussian
soundness against the entire union, and name a rule from a fixed finite subset of `F`. The
square-root protocol reveals at most `K + O_K(ε⁻²)` orthonormal directions.

**Formalization Note** The finite rule alphabet `F₀ ⊆ F` and the constant `C` are chosen after
`F, η, ε` and before `d, δ`; `C_K` after `K` only. In the square-root row the message is a rule
together with a frame of at most `N ≤ K + C_K/ε²` columns, and the verifier rejects every message
whose frame is not orthonormal. -/
theorem theorem_A_5_upper {K : ℕ} (hK : 1 ≤ K) :
    ∃ CK : ℝ, ∀ F : Set (Vec K → Bool), F.Nonempty → (∀ f ∈ F, Measurable f) →
    GaussTotallyBounded F → ∀ η : ℝ, 0 < η → η < 1 / 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ((∀ f ∈ F, ∀ g ∈ F, ∀ A : Matrix (Fin K) (Fin K) ℝ, IsContraction A →
          Jprog 0 f g A η ≤ 0) →
        ∃ (C : ℝ) (F₀ : Finset (Vec K → Bool)), (↑F₀ : Set (Vec K → Bool)) ⊆ F ∧
          ∀ d : ℕ, K ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∃ (Msg : Type) (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg),
              ProperIn V (↑F₀ : Set (Vec K → Bool)) ∧ OMSound V (projClass F d) ε δ ∧
              OMMassartComplete V Hon (projClass F d) η ε δ ∧
              (V.m : ℝ) ≤ C * Real.log (1 / δ) ∧ (Hon.mP : ℝ) ≤ C * (d + Real.log (1 / δ))) ∧
      ((∀ f ∈ F, ∀ g ∈ F, ∀ A : Matrix (Fin K) (Fin K) ℝ, IsContraction A →
          Jprog 1 f g A η ≤ 0) →
        ∃ (C : ℝ) (F₀ : Finset (Vec K → Bool)) (N : ℕ), (↑F₀ : Set (Vec K → Bool)) ⊆ F ∧
          (N : ℝ) ≤ K + CK / ε ^ 2 ∧ ∀ d : ℕ, K ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∃ (V : OneMsgVerifier d ((Vec K → Bool) × FrameMsg d N))
              (Hon : HonestProver d ((Vec K → Bool) × FrameMsg d N)),
              ProperIn V (↑F₀ : Set (Vec K → Bool)) ∧ ChecksFrame V Prod.snd ∧
              OMSound V (projClass F d) ε δ ∧ OMMassartComplete V Hon (projClass F d) η ε δ ∧
              (V.m : ℝ) ≤ C * Real.sqrt d * Real.log (1 / δ) ∧
              (Hon.mP : ℝ) ≤ C * (d + Real.log (1 / δ))) ∧
      (∃ (C : ℝ) (F₀ : Finset (Vec K → Bool)), (↑F₀ : Set (Vec K → Bool)) ⊆ F ∧
        ∀ d : ℕ, K ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
          ∃ (Msg : Type) (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg),
            ProperIn V (↑F₀ : Set (Vec K → Bool)) ∧ OMSound V (projClass F d) ε δ ∧
            OMMassartComplete V Hon (projClass F d) η ε δ ∧
            (V.m : ℝ) ≤ C * (d + Real.log (1 / δ)) ∧
            (Hon.mP : ℝ) ≤ C * (d + Real.log (1 / δ))) := by sorry

end CondGeoVerif
