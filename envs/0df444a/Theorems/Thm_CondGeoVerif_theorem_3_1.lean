-- Prove2me | Theorems.Thm_CondGeoVerif_theorem_3_1
-- name    : CondGeoVerif.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:40:46.218198+00:00
-- url     : https://prove2.me/theorems/e4b0f9ef-8764-46e2-b01f-e947e53cc4f7
-- title:
--   Theorem 3.1 — sharp dimension classification: $O(1)$, $\Theta(\sqrt d)$ or $\Theta(d)$ private verifier samples
-- statement:
--   Fix a nonempty family $F$ of Borel rules $\mathbb R^k\to\{-1,1\}$, $k\ge1$, totally bounded in Gaussian disagreement, and a noise bound $0<\eta<1/2$. Conditions range over every ordered pair $f,g\in F$ and every contraction $A$.
--
--   1. **Upper bounds.** For every accuracy $0<\varepsilon<1$ there are a constant $C$ and a finite rule alphabet $F_0\subseteq F$, depending on $F,k,\eta,\varepsilon$, such that for every $d\ge k$ and $0<\delta\le1/4$ there is a proper one-message verifier with outputs from $F_0$, full Massart completeness with an honest independent sample-only prover, and arbitrary-label Gaussian soundness against $\mathcal H_{F,d}$, whose private sample count is
--
--   | condition | upper bound |
--   |---|---|
--   | $J_0(f,g,A;\eta)\le0$ everywhere | $C\log(1/\delta)$ |
--   | $J_1(f,g,A;\eta)\le0$ everywhere | $C\sqrt d\log(1/\delta)$ |
--   | no additional condition | $C(d+\log(1/\delta))$ |
--
--   and whose honest prover uses at most $C(d+\log(1/\delta))$ observations.
--   2. **Lower bounds.** If $J_j(f,g,A;\eta)=\Gamma>0$ for some $f,g\in F$, contraction $A$ and $j\in\{0,1\}$, then for every $0<\varepsilon\le\Gamma/8$ there are $c>0$ and an additive validation cost $L$ such that for all $d\ge2k$ every interactive, possibly improper verifier that is complete with probability $2/3$ at the single known random-noise anchor $Q$ ($\mathbb E_Q[Y\mid X]=af(X_1,\dots,X_k)$) and sound with probability $2/3$ against all Gaussian-marginal labels satisfies $c\sqrt d\le m_V+L$ if $j=0$ and $c\,d\le m_V+L$ if $j=1$.
--   3. **Exhaustiveness.** $J_1(f,g,A;\eta)\le J_0(f,g,A;\eta)$ for all $f,g\in F$ and contractions $A$.
--
--   Hence, at constant confidence and sufficiently small fixed accuracy, the exhaustive dimension classification is: $J_0\le0$ everywhere gives a dimension-independent count; $\sup J_0>0$ with $J_1\le0$ everywhere gives $\Theta(\sqrt d)$; $\sup J_1>0$ gives $\Theta(d)$.
--
--   Differences from the source:
--   - reading: Θ rows "at constant confidence and sufficiently small fixed accuracy" with sup_{f,g,A} J_j > 0 → for every positive witness J_j(f, g, A; η) = Γ and every 0 < ε ≤ Γ/8: ∃ c > 0, ∃ L, ∀ d ≥ 2k, c√d ≤ m_V + L (j = 0) or c·d ≤ m_V + L (j = 1); with part 3 and the upper rows this yields the three Θ rows; reason: the paragraph after the theorem: "a positive witness J_j(f,g,A;η) = Γ gives the lower bound for fixed ε ≤ Γ/8, with an additive validation cost depending on Γ"; a positive supremum supplies a witness, and this explicit reading is the stronger one
--   - reading: constant confidence; 0 < δ ≤ 1/4 → upper rows for every 0 < δ ≤ 1/4; lower rows for verifiers complete and sound with probability 2/3 (δ = 1/3, the level of Theorem B.1); reason: a verifier with any confidence δ ≤ 1/3 is also a 2/3 verifier
--   - reading: any verifier with arbitrary interaction → IVerifier: a fixed worst-case number of rounds, measurable queries and acceptance, jointly measurable output predictors; reason: the probabilities of Definition 2.1 are defined only for measurable protocols, outputs are 'measurable Boolean predictors', and bounded stopping rules are padded (p.28)
--   - generalization: soundness against every prover → soundness hypothesis only against measurable deterministic prover strategies; reason: a weaker hypothesis; the proof's simulated honest prover is a measurable randomized strategy, a mixture of deterministic ones
--   - generalization: soundness for every prover strategy → soundness for every fixed message, of any type and with no measurability in the message; reason: a random message sent before the private sample is a mixture of fixed messages, and a malicious prover may know the law; the printed requirement follows
--   - reading: one-message protocols whose probabilities "include the samples and all protocol randomness" → for each message the acceptance bit is measurable in (sample, coins) and the output predictor jointly measurable in (sample, coins, feature); the honest run is jointly measurable in (prover sample, prover coins, verifier sample, verifier coins); reason: the probabilities of Definition 2.1 are defined only for measurable protocols, and improper outputs are 'measurable Boolean predictors'
--   - encoding: O(·) bounds with constants depending on the fixed parameters; Massart noise P(Y ≠ h*(X) | X) ≤ η a.s. → ∃ C chosen after the fixed parameters and before d, δ; Massart as P({X ∈ B, Y ≠ h*(X)}) ≤ η·N(0,I_d)(B) for Borel B; reason: Lean convention; equivalent statements
--   - encoding: the null Q: X ∼ N(0, I_d), E_Q[Y | X] = af(X₁, …, X_k) → any probability measure with IsLabelLaw for the base rule f(X₁, …, X_k) and constant error probability η; reason: this property determines Q uniquely
--   - encoding: contraction ‖A‖_op ≤ 1; B_A = (I_k − AᵀA)^{1/2}; J_j an expectation → I − AᵀA positive semidefinite; the CFC square root; a Bochner integral whose integrand is measurable by Lemma B.2; reason: equivalent; Lean convention
--   - encoding: labels and rule values in {−1, 1} → Bool, with true for +1; reason: Lean convention; the same instances
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem 3.1, p.5 (PDF p.8), with the paragraph after it

import Mathlib
import Definitions.Def_CondGeoVerif_Jprog
import Definitions.Def_CondGeoVerif_GaussTotallyBounded
import Definitions.Def_CondGeoVerif_OneMsgVerifier
import Definitions.Def_CondGeoVerif_IVerifier

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **Theorem 3.1 (Sharp dimension classification)** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, p.5 = PDF p.8). Fix a
nonempty totally bounded family `F` of Borel rules `ℝᵏ → {−1, 1}`, `k ≥ 1`, a noise bound
`0 < η < 1/2`, and write `H_{F,d}` for its projection class in dimension `d`.
1. (Upper bounds.) For every accuracy `0 < ε < 1` there are a constant `C` and a finite rule
   alphabet `F₀ ⊆ F` (depending on `F, k, η, ε`) such that for every `d ≥ k` and `0 < δ ≤ 1/4`
   there is a proper one-message verifier with outputs from `F₀`, full Massart completeness with
   an honest independent sample-only prover, and arbitrary-label Gaussian soundness against
   `H_{F,d}`, whose private sample count is at most `C log(1/δ)` if `J₀(f, g, A; η) ≤ 0`
   everywhere, at most `C√d log(1/δ)` if `J₁(f, g, A; η) ≤ 0` everywhere, and at most
   `C(d + log(1/δ))` with no condition; the honest prover uses at most `C(d + log(1/δ))`
   observations.
2. (Lower bounds.) If `J₀(f, g, A; η) > 0` (resp. `J₁(f, g, A; η) > 0`) for some `f, g ∈ F` and a
   contraction `A`, then for every `0 < ε ≤ J_j(f, g, A; η)/8` there are `c > 0` and an additive
   validation cost `L` such that for all `d ≥ 2k`, every interactive, possibly improper verifier
   that is complete with probability `2/3` at the single known random-noise anchor
   (`E_Q[Y | X] = af(X₁, …, X_k)`) and sound with probability `2/3` against all Gaussian-marginal
   labels has `c√d ≤ m_V + L` (resp. `c·d ≤ m_V + L`).
3. (Exhaustiveness.) `J₁(f, g, A; η) ≤ J₀(f, g, A; η)` for all `f, g ∈ F` and contractions `A`.
Hence the classification: `J₀ ≤ 0` everywhere gives a dimension-independent count;
`sup J₀ > 0`, `J₁ ≤ 0` everywhere gives `Θ(√d)`; `sup J₁ > 0` gives `Θ(d)`.

**Formalization Note** Conditions range over every ordered pair `f, g ∈ F` and every contraction
`A`. `O(·)` constants are chosen after `ε` and before `d, δ`; the lower-bound constants after the
witness and `ε` and before `d`. A positive supremum yields a positive witness, and `L` is absorbed
for large `d`, so the `Θ` rows follow from parts 1–3. The anchor is given through its
characterizing property `IsLabelLaw`. -/
theorem theorem_3_1 {k : ℕ} (hk : 1 ≤ k) (F : Set (Vec k → Bool)) (hFne : F.Nonempty)
    (hFm : ∀ f ∈ F, Measurable f) (hFtb : GaussTotallyBounded F) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / 2) :
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      ((∀ f ∈ F, ∀ g ∈ F, ∀ A : Matrix (Fin k) (Fin k) ℝ, IsContraction A →
          Jprog 0 f g A η ≤ 0) →
        ∃ (C : ℝ) (F₀ : Finset (Vec k → Bool)), (↑F₀ : Set (Vec k → Bool)) ⊆ F ∧
          ∀ d : ℕ, k ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∃ (Msg : Type) (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg),
              ProperIn V (↑F₀ : Set (Vec k → Bool)) ∧ OMSound V (projClass F d) ε δ ∧
              OMMassartComplete V Hon (projClass F d) η ε δ ∧
              (V.m : ℝ) ≤ C * Real.log (1 / δ) ∧ (Hon.mP : ℝ) ≤ C * (d + Real.log (1 / δ))) ∧
      ((∀ f ∈ F, ∀ g ∈ F, ∀ A : Matrix (Fin k) (Fin k) ℝ, IsContraction A →
          Jprog 1 f g A η ≤ 0) →
        ∃ (C : ℝ) (F₀ : Finset (Vec k → Bool)), (↑F₀ : Set (Vec k → Bool)) ⊆ F ∧
          ∀ d : ℕ, k ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∃ (Msg : Type) (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg),
              ProperIn V (↑F₀ : Set (Vec k → Bool)) ∧ OMSound V (projClass F d) ε δ ∧
              OMMassartComplete V Hon (projClass F d) η ε δ ∧
              (V.m : ℝ) ≤ C * Real.sqrt d * Real.log (1 / δ) ∧
              (Hon.mP : ℝ) ≤ C * (d + Real.log (1 / δ))) ∧
      (∃ (C : ℝ) (F₀ : Finset (Vec k → Bool)), (↑F₀ : Set (Vec k → Bool)) ⊆ F ∧
        ∀ d : ℕ, k ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
          ∃ (Msg : Type) (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg),
            ProperIn V (↑F₀ : Set (Vec k → Bool)) ∧ OMSound V (projClass F d) ε δ ∧
            OMMassartComplete V Hon (projClass F d) η ε δ ∧
            (V.m : ℝ) ≤ C * (d + Real.log (1 / δ)) ∧
            (Hon.mP : ℝ) ≤ C * (d + Real.log (1 / δ)))) ∧
    (∀ f ∈ F, ∀ g ∈ F, ∀ A : Matrix (Fin k) (Fin k) ℝ, IsContraction A →
      0 < Jprog 0 f g A η → ∀ ε : ℝ, 0 < ε → ε ≤ Jprog 0 f g A η / 8 →
        ∃ (c : ℝ) (L : ℕ), 0 < c ∧ ∀ d : ℕ, 2 * k ≤ d → ∀ V : IVerifier d,
          ∀ Q : ProbabilityMeasure (Vec d × Bool),
            IsLabelLaw (Q : Measure (Vec d × Bool)) (frameRule f (coordFrame d k)) (fun _ => η) →
            ICompleteAt V Q (projClass F d) ε (1 / 3) → ISound V (projClass F d) ε (1 / 3) →
              c * Real.sqrt d ≤ (V.m : ℝ) + L) ∧
    (∀ f ∈ F, ∀ g ∈ F, ∀ A : Matrix (Fin k) (Fin k) ℝ, IsContraction A →
      0 < Jprog 1 f g A η → ∀ ε : ℝ, 0 < ε → ε ≤ Jprog 1 f g A η / 8 →
        ∃ (c : ℝ) (L : ℕ), 0 < c ∧ ∀ d : ℕ, 2 * k ≤ d → ∀ V : IVerifier d,
          ∀ Q : ProbabilityMeasure (Vec d × Bool),
            IsLabelLaw (Q : Measure (Vec d × Bool)) (frameRule f (coordFrame d k)) (fun _ => η) →
            ICompleteAt V Q (projClass F d) ε (1 / 3) → ISound V (projClass F d) ε (1 / 3) →
              c * (d : ℝ) ≤ (V.m : ℝ) + L) ∧
    (∀ f ∈ F, ∀ g ∈ F, ∀ A : Matrix (Fin k) (Fin k) ℝ, IsContraction A →
      Jprog 1 f g A η ≤ Jprog 0 f g A η) := by sorry

end CondGeoVerif
