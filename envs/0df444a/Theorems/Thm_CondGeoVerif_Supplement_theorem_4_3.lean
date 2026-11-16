-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_4_3
-- name    : CondGeoVerif.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:12:24.14021+00:00
-- url     : https://prove2.me/theorems/032a7e3f-9aea-4749-8635-d5304b18cc1e
-- title:
--   Theorem 4.3 — matched balanced quadratic separation: $Q_{0,d}$ needs $O(\varepsilon^{-1}\log(e/\varepsilon))$, $Q_{t,d}$ needs $\Theta_{\eta,\varepsilon}(d)$ private samples
-- statement:
--   Let $f_t(s,u)=\mathrm{sign}(s)\,\mathrm{sign}(u-t)$ and, for $d\ge2$, $Q_{t,d}=\{x\mapsto f_t(v\cdot x,w\cdot x):\|v\|=\|w\|=1,\ v\perp w\}$, with features $X\sim N(0,I_d)$. There is $\eta^*>0$ such that, for every fixed $0<\eta\le\eta^*$, choosing $t=\Phi^{-1}(1-\eta/2)$ gives, at constant confidence and every fixed $0<\varepsilon\le\eta^2/8$:
--
--   | class | private verifier samples |
--   |---|---|
--   | $Q_{0,d}$ | $O(\varepsilon^{-1}\log(e/\varepsilon))$ |
--   | $Q_{t,d}$ | $\Theta_{\eta,\varepsilon}(d)$ |
--
--   Both classes have Gaussian positive prevalence $1/2$, minimum projection rank two, minimum polynomial threshold degree two, and VC dimension $\Theta(d)$. Both guarantees use the same feature law and noise bound $\eta$, with full Massart completeness and arbitrary-label soundness. The lower bound allows interaction and improper outputs.
--
--   Precisely: the upper bounds are proper one-message verifiers (outputs in the class) with an honest prover, full Massart completeness at noise bound $\eta$ and arbitrary-label Gaussian soundness, both with failure probability $1/4$; the constant in the $Q_{0,d}$ row does not depend on $\eta$ or $\varepsilon$. The lower bound gives $c>0$ and $L$ (depending on $\eta,\varepsilon$) with $c\,d\le m_V+L$ for all $d\ge2$ and every interactive, possibly improper verifier that is complete with probability $2/3$ at the random-noise anchor $\mathbb E[Y\mid X]=(1-2\eta)f_t(X_1,X_2)$ and sound with probability $2/3$ against all Gaussian-marginal labels.
--
--   A single offset $t$ therefore changes the dimension exponent while preserving the usual measures of class complexity.
--
--   Differences from the source:
--   - reading: constant confidence → upper bounds at failure probability δ = 1/4; lower bound for verifiers complete and sound with probability 2/3; reason: the convention of the live goal Theorem 3.1 (paper.md decision 4)
--   - generalization: the Θ lower bound for verifiers with full Massart completeness → for every verifier complete (probability 2/3) only at the known random-noise anchor E[Y | X] = (1 − 2η) f_t(X₁, X₂); reason: the anchor is a Massart law around a member of Q_{t,d}, so every fully complete verifier is complete there; this is the hypothesis of Theorem B.1 used in the proof
--   - encoding: Θ_{η,ε}(d) lower part → ∃ c > 0, L with c·d ≤ m_V + L for all d ≥ 2; reason: witness form of the live goal; L absorbs finitely many small d
--   - reading: any verifier with arbitrary interaction and every prover strategy → the published IVerifier (finitely many rounds, measurable queries and outputs) and soundness against every measurable prover strategy; reason: same model as the live goal Theorem 3.1 and Theorem B.1; the paper's simulated honest prover is a measurable randomized strategy
--   - encoding: t = Φ⁻¹(1 − η/2) → every t with Φ(t) = 1 − η/2; reason: Φ is a continuous strictly increasing bijection onto (0, 1), so t is unique and exists
--   - encoding: VC dimension Θ(d) → ∃ c, C > 0, d₀: for d ≥ d₀ some finite set of size ≥ c·d is shattered and no finite set of size > C·d is; reason: the definition of VC dimension by shattered finite sets
--   - encoding: minimum projection rank and minimum polynomial threshold degree → read up to Gaussian-null sets; reason: as in the proof of Lemma C.12 (p.36–37)
--   - encoding: labels in {−1, 1}; a sign on a zero hyperplane can be chosen arbitrarily → labels Bool (true ↔ +1), sign(0) = +1; reason: hyperplanes are Gaussian-null, so no probability in the statement depends on the convention (App. C, p.28)
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem 4.3, p.9 (PDF p.12); proof in §C.7, pp.36–37 (Proposition C.11, Lemma C.12)

import Mathlib
import Definitions.Def_CondGeoVerif_IVerifier
import Definitions.Def_HighDimProb_Chaining_Shatters
import Definitions.Def_CondGeoVerif_Supplement_critA
import Definitions.Def_CondGeoVerif_Supplement_boolComp
import Definitions.Def_CondGeoVerif_Supplement_MinProjRank

set_option autoImplicit false

open MeasureTheory Cohen2019.Robust HighDimProb.Chaining

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem 4.3 (Matched balanced quadratic separation)** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, p.9 = PDF p.12). There is
`η* > 0` such that, for every fixed `0 < η ≤ η*`, choosing `t = Φ⁻¹(1 − η/2)` gives, at constant
confidence and every fixed `0 < ε ≤ η²/8`: the parity class `Q_{0,d}` has private verifier sample
complexity `O(ε⁻¹ log(e/ε))` and the shifted parity class `Q_{t,d}` has `Θ_{η,ε}(d)`. Both classes
have Gaussian positive prevalence `1/2`, minimum projection rank two, minimum polynomial threshold
degree two, and VC dimension `Θ(d)`. Both guarantees use the same feature law `N(0, I_d)` and noise
bound `η`, with full Massart completeness and arbitrary-label soundness. The lower bound allows
interaction and improper outputs.

**Formalization Note** Here `Q_{t,d} = parityClass t d`, `d ≥ 2`. `t = Φ⁻¹(1 − η/2)` is given by its
defining equation `Φ(t) = 1 − η/2` (unique, `Φ` is strictly increasing). Upper bounds at constant
confidence are proper one-message verifiers at `δ = 1/4`; the `O(ε⁻¹ log(e/ε))` constant `C₀` is
chosen before `η` and `ε`, the `Θ_{η,ε}(d)` constants after them. The lower bound is in witness form
`c·d ≤ m_V + L` (as in the live goal), for every interactive improper verifier complete with
probability `2/3` at the known random-noise anchor `E[Y | X] = (1 − 2η)f_t(X₁, X₂)` (a Massart law
around a member of `Q_{t,d}`) and sound with probability `2/3` against all Gaussian-marginal labels.
The structural claims hold for every member of both classes in every dimension `d ≥ 2`; VC
dimension `Θ(d)` is stated with shattered finite sets: some set of size `≥ c·d` is shattered and no
set of size `> C·d` is, for all `d ≥ d₀`. -/
theorem theorem_4_3 :
    ∃ ηs : ℝ, 0 < ηs ∧ ∃ C0 : ℝ, ∀ η : ℝ, 0 < η → η ≤ ηs → ∀ t : ℝ, Phi t = 1 - η / 2 →
      ∀ ε : ℝ, 0 < ε → ε ≤ η ^ 2 / 8 →
        (∀ d : ℕ, 2 ≤ d → ∃ (Msg : Type) (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg),
          ProperIn V ({parityRule 0} : Set (Vec 2 → Bool)) ∧
          OMSound V (parityClass 0 d) ε (1 / 4) ∧
          OMMassartComplete V Hon (parityClass 0 d) η ε (1 / 4) ∧
          (V.m : ℝ) ≤ C0 * (1 / ε) * Real.log (Real.exp 1 / ε)) ∧
        (∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → ∃ (Msg : Type) (V : OneMsgVerifier d Msg)
            (Hon : HonestProver d Msg),
          ProperIn V ({parityRule t} : Set (Vec 2 → Bool)) ∧
          OMSound V (parityClass t d) ε (1 / 4) ∧
          OMMassartComplete V Hon (parityClass t d) η ε (1 / 4) ∧
          (V.m : ℝ) ≤ C * d) ∧
        (∃ (c : ℝ) (L : ℕ), 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ V : IVerifier d,
          ∀ Q : ProbabilityMeasure (Vec d × Bool),
            IsLabelLaw (Q : Measure (Vec d × Bool)) (frameRule (parityRule t) (coordFrame d 2))
              (fun _ => η) →
            ICompleteAt V Q (parityClass t d) ε (1 / 3) → ISound V (parityClass t d) ε (1 / 3) →
              c * (d : ℝ) ≤ (V.m : ℝ) + L) ∧
        (∀ t' ∈ ({0, t} : Set ℝ), ∀ d : ℕ, 2 ≤ d → ∀ h ∈ parityClass t' d,
          posPrevalence h = 1 / 2 ∧ MinProjRank h 2 ∧ MinPTFDegree h 2) ∧
        (∀ t' ∈ ({0, t} : Set ℝ), ∃ (c C : ℝ) (d0 : ℕ), 0 < c ∧ 0 < C ∧ ∀ d : ℕ, d0 ≤ d →
          (∃ S : Finset (Vec d), c * d ≤ (S.card : ℝ) ∧ Shatters (parityClass t' d) (↑S : Set (Vec d))) ∧
          ∀ S : Finset (Vec d), Shatters (parityClass t' d) (↑S : Set (Vec d)) →
            (S.card : ℝ) ≤ C * d) := by sorry

end CondGeoVerif.Supplement
