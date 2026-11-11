-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_9
-- name    : DPCutRelease.Main.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:12:21.804285+00:00
-- url     : https://prove2.me/theorems/097f790b-94cf-437c-a60a-fcb3f9e9ee30
-- title:
--   Lemma 9 — advanced adaptive composition: (ε₀√(2k ln(1/δ′)) + kε₀(e^{ε₀} − 1), kδ₀ + δ′) edge-DP
-- statement:
--   Let $M_1,\dots,M_k$ be adaptively chosen mechanisms (Markov kernels $\kappa_w^{(i)}$ on transcript prefixes, as in Lemma 8) such that, conditional on every fixed preceding transcript, each $M_i$ is $(\varepsilon_0,\delta_0)$ edge-DP, for some $\varepsilon_0>0$ and $\delta_0\ge0$. Then for every $\delta'\in(0,1)$ the adaptive composition is $(\varepsilon,k\delta_0+\delta')$ edge-DP, where
--   $$\varepsilon=\varepsilon_0\sqrt{2k\ln(1/\delta')}+k\varepsilon_0\big(e^{\varepsilon_0}-1\big).$$
--   This is the composition of the $T_2$ calls of AggregateWitnesses inside one outer round of Algorithm 1 (Lemma 18).
--
--   **Formalization Note.** Same conventions as Lemma 8; `Real.log` is the natural logarithm.
--
--   Differences from the source:
--   - reading: "conditional on every fixed preceding transcript, each Mᵢ is (ε₀, δ₀)-DP" → each kernel κ w i y is (ε₀, δ₀) edge-DP for every prefix y; reason: literal rendering with Markov kernels on prefixes
--   - encoding: Pr[M(w) ∈ A] ≤ e^ε Pr[M(w′) ∈ A] + δ for adjacent w, w′ and measurable A, and symmetrically → IsEdgeDP / IsEdgeDPFun: the inequality between real numbers (toReal) for every ordered adjacent pair; reason: adjacency is symmetric, so the swapped clause is the same condition; every law involved is a probability measure
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 11, Lemma 9

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_Adaptive

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 9 (Advanced Adaptive Composition, p. 11): if, conditional on every preceding
transcript, each of `k` adaptively chosen mechanisms is `(ε₀, δ₀)` edge-DP with `ε₀ > 0`, `δ₀ ≥ 0`,
then for every `δ' ∈ (0, 1)` the transcript is `(ε₀ √(2k ln(1/δ')) + k ε₀ (e^{ε₀} − 1), k δ₀ + δ')`
edge-DP. -/
theorem lemma_9 {n : ℕ} {Y : Type*} [MeasurableSpace Y] (k : ℕ)
    (κ : EdgeVec n → (i : ℕ) → Kernel (Fin i → Y) Y) [∀ w i, IsMarkovKernel (κ w i)]
    (ε0 δ0 δ' : ℝ) (hε0 : 0 < ε0) (hδ0 : 0 ≤ δ0) (hδ'0 : 0 < δ') (hδ'1 : δ' < 1)
    (hDP : ∀ i < k, ∀ y : Fin i → Y, IsEdgeDP (fun w => κ w i y) ε0 δ0) :
    IsEdgeDP (fun w => transcriptLaw (κ w) k)
      (ε0 * Real.sqrt (2 * k * Real.log (1 / δ')) + k * ε0 * (Real.exp ε0 - 1))
      (k * δ0 + δ') := by sorry

end DPCutRelease.Main
