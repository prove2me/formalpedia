-- Prove2me | Theorems.Thm_BauerleRiederMDP_Indifference_remark_4_9_3_measure
-- name    : BauerleRiederMDP.Indifference.remark_4_9_3_measure
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:53.629942+00:00
-- url     : https://prove2.me/theorems/b096db0b-dec6-4f4a-8025-23790f00738f
-- title:
--   Remark 4.9.3 — $\mathbb Q$ is a probability measure with (i), (ii), and is risk neutral on $\sigma(\tilde R)$
-- statement:
--   For the measure $\mathbb Q$ of Remark 4.9.3 and initial prices $S_0=s>0$, $\hat S_0=\hat s>0$, so that $S_1=s\tilde R$ and $\hat S_1=\hat s\hat R$:
--
--   1. $\mathbb Q$ is a probability measure on $\Omega$;
--   2. (i) $\mathbb E_{\mathbb Q}S_1=S_0$;
--   3. (ii) $\mathbb Q(\hat S_1\in B\mid S_1)=\mathbb P(\hat S_1\in B\mid S_1)$ for all $B\subset\{\hat s\hat d,\hat s\hat u\}$;
--   4. $\mathbb Q$ coincides on the $\sigma$-algebra $\{\emptyset,\Omega,\{\omega_1,\omega_2\},\{\omega_3,\omega_4\}\}$ with the unique risk neutral measure of the binomial model: the only $q'$ with $q'u+(1-q')d=1$ is $q$, and $\mathbb Q(\{\omega_1,\omega_2\})=q'$, $\mathbb Q(\{\omega_3,\omega_4\})=1-q'$.
--
--   Thus $\mathbb Q$ changes the law of the traded asset to the risk neutral one and leaves the conditional law of the non-traded asset unchanged.
--
--   **Formalization Note** The conditional probabilities are conditional expectations of an indicator given $\sigma(S_1)$; the equality holds $\mathbb P$-almost surely.
--
--   Differences from the source:
--   - generalization: (i) for the initial price S₀ = s > 0 → (i) for every real s; reason: the identity is linear in s; the book's case is included
--   - reading: Q coincides with the unique risk neutral measure of the binomial model (the model of §3.1 with i = 0, up factor u, down factor d) → the up probability q' with q'u + (1 − q')d = 1 is unique, equals q, and is the Q-mass of {ω₁, ω₂}; reason: the binomial risk neutral measure is determined by its up probability, and the page does not write it out
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 4.9.3, p.137

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_Q

open MeasureTheory

namespace BauerleRiederMDP.Indifference

/-- Remark 4.9.3, first part (Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), Remark 4.9.3, p.137, PDF 151). `ℚ` is a probability measure on `Ω`, (i)
`𝔼_ℚ S₁ = S₀`, (ii) `ℚ(Ŝ₁ ∈ B | S₁) = ℙ(Ŝ₁ ∈ B | S₁)` for all `B ⊂ {ŝ d̂, ŝ û}`, and `ℚ` coincides on
the σ-algebra `{∅, Ω, {ω₁, ω₂}, {ω₃, ω₄}}` with the unique risk neutral measure of the binomial model.

**Formalization Note.** `S₀ = s`, `Ŝ₀ = ŝ`, `S₁ = s R̃`, `Ŝ₁ = ŝ R̂` with `s, ŝ > 0`. The conditional
probabilities are the conditional expectations of the indicator of `{Ŝ₁ ∈ B}` given `σ(S₁)`, equal
`ℙ`-a.s. The binomial model has the up probability `q'` with `q' u + (1 - q') d = 1` (zero interest);
the last clause says that this `q'` is unique and is the `ℚ`-mass of `{ω₁, ω₂}`. -/
theorem remark_4_9_3_measure (M : Market) :
    IsProbabilityMeasure M.Q ∧
    (∀ s : ℝ, ∫ ω, s * M.Rt ω ∂M.Q = s) ∧
    (∀ s ŝ : ℝ, 0 < s → 0 < ŝ → ∀ B : Set ℝ, B ⊆ {ŝ * M.dhat, ŝ * M.uhat} →
      M.Q[({ω | ŝ * M.Rh ω ∈ B} : Set (Fin 4)).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (fun ω => s * M.Rt ω) inferInstance] =ᵐ[M.P]
        M.P[({ω | ŝ * M.Rh ω ∈ B} : Set (Fin 4)).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (fun ω => s * M.Rt ω) inferInstance]) ∧
    (∀ q' : ℝ, q' * M.u + (1 - q') * M.d = 1 →
      q' = M.q ∧ M.Q {0, 1} = ENNReal.ofReal q' ∧ M.Q {2, 3} = ENNReal.ofReal (1 - q')) := by sorry

end BauerleRiederMDP.Indifference
