-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_F_5
-- name    : CondGeoVerif.Supplement.theorem_F_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:18:55.370246+00:00
-- url     : https://prove2.me/theorems/c6e668cf-86c1-41f5-ae6b-d35f7386715b
-- title:
--   Theorem F.5 (= 4.5) — slabs: $m_V\le C[d+\varepsilon^{-1}\log\frac{e}{\varepsilon\delta}]$; under (F.3) $m_V\ge[d+\varepsilon^{-1}\log\frac1\delta]/400$
-- statement:
--   Fix $t>0$, $p=2\Phi(t)-1$, $\eta_c=\bar\Phi(\sqrt{2\log2})$ and $0<\eta<\eta_c$; features $X\sim N(0,I_d)$, class $S_{t,d}$ of centered slabs. There are positive constants $C_{t,\eta}$ and $\varepsilon_{t,\eta}$ such that for every $d\ge2$, $0<\varepsilon\le\varepsilon_{t,\eta}$ and $0<\delta\le1/4$, a proper one-message verifier has full Massart completeness and arbitrary-label soundness with
--   $$m_V\le C_{t,\eta}\Big[d+\frac1\varepsilon\log\frac e{\varepsilon\delta}\Big],\qquad m_P\le C_{t,\eta}\frac{d\log(e/\varepsilon)+\log(1/\delta)}{\varepsilon^2}.$$
--   The message is just a unit normal. If additionally
--   $$p(1-p)<\eta,\qquad(F.3)$$
--   then, after decreasing $\varepsilon_{t,\eta}$ if necessary, every verifier in this model (interactive, possibly improper, complete with probability $\ge1-\delta$ under full Massart noise $\le\eta$ and sound with failure $\le\delta$ against arbitrary Gaussian-marginal labels) satisfies
--   $$m_V\ge\frac1{400}\Big[d+\frac1\varepsilon\log\frac1\delta\Big].$$
--   Under (F.3) the optimal rate is therefore $\widetilde\Theta_{t,\eta}(d+\varepsilon^{-1})$: dimension and accuracy costs add.
--
--   Differences from the source:
--   - generalization: every verifier in this model (complete under full Massart noise with an honest prover) → every IVerifier that is complete, in the sense of ICompleteAt, at each Gaussian-marginal law with Massart noise ≤ η around a member of S_{t,d}, where the honest prover may depend on the law; reason: a verifier with one law-independent honest prover satisfies this hypothesis, so the Lean bound specializes to the paper's
--   - reading: any verifier with arbitrary interaction and every prover strategy → the published IVerifier (finitely many rounds, measurable queries and outputs) and soundness against every measurable prover strategy; reason: same model as the live goal Theorem 3.1 and Theorem B.1; the paper's simulated honest prover is a measurable randomized strategy
--   - encoding: the message is just a unit normal → message type ℝ^d; every output h comes with ‖w‖ = 1 and h = h_w for the message w; reason: the paper's message, made a type
--   - encoding: after decreasing ε_{t,η} if necessary → a threshold ε₁ ∈ (0, ε_{t,η}] chosen before d, ε, δ; reason: the decreased threshold
--   - encoding: labels in {−1, 1}; a sign on a zero hyperplane can be chosen arbitrarily → labels Bool (true ↔ +1), sign(0) = +1; reason: hyperplanes are Gaussian-null, so no probability in the statement depends on the convention (App. C, p.28)
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem F.5 and (F.3), p.49 (PDF p.52); formal version of Theorem 4.5, p.10 (PDF p.13); proofs §F.6–F.7, pp.52–56

import Mathlib
import Definitions.Def_CondGeoVerif_IVerifier
import Definitions.Def_CondGeoVerif_Supplement_critA
import Definitions.Def_CondGeoVerif_Supplement_boolComp

set_option autoImplicit false

open MeasureTheory Cohen2019.Robust

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem F.5 (Additive joint complexity)** (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, p.49 = PDF p.52; the formal version of
Theorem 4.5, p.10). Fix `t > 0`, `p = 2Φ(t) − 1`, and `0 < η < η_c = Φ̄(√(2 log 2))`. There are
positive constants `C_{t,η}` and `ε_{t,η}` such that for every `d ≥ 2`, `0 < ε ≤ ε_{t,η}` and
`0 < δ ≤ 1/4`, a proper one-message verifier for centered slabs `S_{t,d}` has full Massart
completeness and arbitrary-label soundness with
`m_V ≤ C_{t,η}[d + ε⁻¹ log(e/(εδ))]` and `m_P ≤ C_{t,η}(d log(e/ε) + log(1/δ))/ε²`; the message is
just a unit normal. If additionally `p(1 − p) < η` (F.3), then, after decreasing `ε_{t,η}` if
necessary, every verifier in this model satisfies `m_V ≥ (1/400)[d + ε⁻¹ log(1/δ)]`.

**Formalization Note** The message type is `ℝᵈ`; whenever the verifier outputs `h`, the message is a
unit vector `w` and `h = h_w`. "Every verifier in this model" is every interactive, possibly
improper `IVerifier` that is complete with probability `≥ 1 − δ` at every Gaussian-marginal law with
Massart noise `≤ η` around a member of `S_{t,d}` (an honest prover may depend on the law) and sound
with failure `≤ δ` against all Gaussian-marginal labels. The decreased accuracy threshold is
`ε₁ ≤ ε_{t,η}`, chosen before `d, ε, δ`. -/
theorem theorem_F_5 {t η : ℝ} (ht : 0 < t) (hη0 : 0 < η) (hη : η < etaC) :
    ∃ C ε0 : ℝ, 0 < C ∧ 0 < ε0 ∧
      (∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ (V : OneMsgVerifier d (Vec d)) (Hon : HonestProver d (Vec d)),
          ProperIn V ({slabRule t} : Set (Vec 1 → Bool)) ∧
          (∀ (w : Vec d) (s : Fin V.m → Vec d × Bool) (ω : V.Ω) (h : Vec d → Bool),
            V.decide w s ω = some h → ‖w‖ = 1 ∧ h = fun x => decide (|inner ℝ w x| ≤ t)) ∧
          OMSound V (slabClass t d) ε δ ∧
          OMMassartComplete V Hon (slabClass t d) η ε δ ∧
          (V.m : ℝ) ≤ C * (d + 1 / ε * Real.log (Real.exp 1 / (ε * δ))) ∧
          (Hon.mP : ℝ) ≤ C * ((d * Real.log (Real.exp 1 / ε) + Real.log (1 / δ)) / ε ^ 2)) ∧
      ((2 * Phi t - 1) * (1 - (2 * Phi t - 1)) < η →
        ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 ≤ ε0 ∧
          ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε1 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∀ V : IVerifier d,
              (∀ Q : ProbabilityMeasure (Vec d × Bool), GaussMarginal (Q : Measure (Vec d × Bool)) →
                ∀ hstar ∈ slabClass t d, IsMassart (Q : Measure (Vec d × Bool)) hstar η →
                  ICompleteAt V Q (slabClass t d) ε δ) →
              ISound V (slabClass t d) ε δ →
                1 / 400 * (d + 1 / ε * Real.log (1 / δ)) ≤ (V.m : ℝ)) := by sorry

end CondGeoVerif.Supplement
