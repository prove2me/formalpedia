-- Prove2me | Theorems.Thm_ActiveSaddleSGD_lemma_13
-- name    : ActiveSaddleSGD.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:50.580679+00:00
-- url     : https://prove2.me/theorems/fdb5b9fb-10a6-4fe4-be49-f312146587db
-- title:
--   Lemma 13 — $\mathbb P_N(\tau_N(L)<+\infty)\ge C_{13}(L)$
-- statement:
--   In the repulsive setting, let $\tau_N(L)=\inf\{k\ge N:U_k^2\ge L\chi_k\}$. For $L>0$, if the quantity $\max(c_{\tilde r,2},c_r^{1/2})\sqrt L$ is small enough, then there is a constant $C_{13}=C_{13}(L)>0$ such that for all $N\in\mathbb N$,
--   $$
--   \mathbb P_N(\tau_N(L)<+\infty)\ge C_{13}(L).
--   $$
--
--   So from any time on, $U_n$ reaches the scale $\sqrt{L\chi_n}$ with conditional probability bounded below: the noise pushes the iterates off the graph.
--
--   **Formalization Note** The event is "there is $k\ge N$ with $L\chi_k\le U_k^2$", which is measurable, and $\mathbb P_N$ is the conditional expectation of its indicator.
--
--   Differences from the source:
--   - reading: "small enough", on $\max(c_{\tilde r,2},c_r^{1/2})\sqrt L$ only → a threshold $\varepsilon$ on that quantity, and thresholds on $c_H$, $c_r$, $c_{\tilde r,1}$; reason: Lemma 11 (p.30) uses that $c_H$, $c_r$, $c_{\tilde r,1}$ are small, as Lemma 9 allows
--   - reading: the threshold $\lambda_{\max}\max(\cdot)\sqrt L\le C_{11}/8$ → $\varepsilon$ existential; reason: the page's constants rest on Lemmas 10 and 11, which are false as printed in their constants
--   - encoding: $C_{13}$ depends on $L,C_{11},C_{12},C_{e,1},c_r,C_{\tilde r}$ → $C_{13}$ chosen after $(\gamma_n)$ and before the sequences; reason: $C_{12}$ contains $\chi_0$ (proof of Lemma 12, p.30)
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Lemma 13, p.31

import Mathlib
import Definitions.Def_ActiveSaddleSGD_ProjectedIterates
import Definitions.Def_ActiveSaddleSGD_CenterStable
import Definitions.Def_ActiveSaddleSGD_Repulsive

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ActiveSaddleSGD

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 13, p.31: for `L > 0`, if
`max(c_{r̃,2}, c_r^{1/2}) √L` is small enough, there is `C₁₃ = C₁₃(L) > 0` such that for all `N`,
`ℙ_N(τ_N(L) < +∞) ≥ C₁₃(L)`, where `τ_N(L) = inf{k ≥ N : U_k² ≥ L χ_k}`.

**Formalization Note** The event `[τ_N(L) < ∞]` is "`∃ k ≥ N, L χ_k ≤ U_k²`", and `ℙ_N` is the conditional
expectation of its indicator; the event is measurable, so that is genuine. "Small enough" is the
threshold `ε`, depending on `J⁻`, `Q` and the `C_·`, not on `L`. `ε` is left existential because the page's
explicit threshold rests on Lemmas 10 and 11, which are false as printed in their constants. As
Lemma 9 has it ("as small as needed"), the proof of Lemma 11 (p.30) also needs `c_H`, `c_r`, `c_{r̃,1}` below
thresholds. `C₁₃` comes before the sequences. It depends on `(γ_n)` through `χ₀`, which enters `C₁₂` (p.30). -/
theorem lemma_13.{v} {m : ℕ} (Jm Q : Matrix (Fin m) (Fin m) ℝ) (hm : 0 < m)
    (hJm : HasNegRealParts Jm) (hQ : Q.PosDef)
    (hL : Q * Jm + Jm.transpose * Q = -(2 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ))
    (Ce1 Ce2 Crt : ℝ) (hCe1 : 0 < Ce1) (hCe2 : 0 < Ce2) (hCrt : 0 < Crt) :
    ∃ cH₀ cr₀ c1₀ ε : ℝ, 0 < cH₀ ∧ 0 < cr₀ ∧ 0 < c1₀ ∧ 0 < ε ∧
      ∀ cH cr cr1 cr2 L : ℝ, 0 < cH → cH ≤ cH₀ → 0 < cr → cr ≤ cr₀ → 0 < cr1 → cr1 ≤ c1₀ →
        0 < cr2 → 0 < L → max cr2 (Real.sqrt cr) * Real.sqrt L ≤ ε →
        ∀ γ : ℕ → ℝ, IsStepSequence γ →
        ∃ C13 > 0,
          ∀ (Ω : Type v) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
            (ℱ : Filtration ℕ mΩ) (w : ℕ → Ω → EuclideanSpace ℝ (Fin m))
            (H : ℕ → Ω → Matrix (Fin m) (Fin m) ℝ)
            (e r rt : ℕ → Ω → EuclideanSpace ℝ (Fin m)),
            RepulsiveSetting μ ℱ γ Jm Q w H e r rt cH Ce1 Ce2 cr Crt cr1 cr2 →
            ∀ N : ℕ, ∀ᵐ ω ∂μ,
              C13 ≤ (μ[Set.indicator {a | ∃ k, N ≤ k ∧ L * tailChi γ k ≤ lyapNorm Q (w k) a ^ 2}
                (fun _ => (1 : ℝ)) | ℱ N]) ω := by sorry

end ActiveSaddleSGD
