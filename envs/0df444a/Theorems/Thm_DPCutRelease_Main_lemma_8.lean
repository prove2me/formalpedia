-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_8
-- name    : DPCutRelease.Main.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:12:19.817199+00:00
-- url     : https://prove2.me/theorems/f7ef9b2a-9393-4eab-85af-30cfe0617e21
-- title:
--   Lemma 8 — basic adaptive composition: (Σεᵢ, Σδᵢ) edge-DP
-- statement:
--   Let $M_1,\dots,M_k$ be adaptively chosen randomized mechanisms with outputs in a measurable space $Y$: for every input $w$ and step $i$ (0-based, $i<k$), $\kappa_w^{(i)}(y_{<i})$ is the law of the $i$-th output given the prefix $y_{<i}$ of earlier outputs. Suppose that at every fixed prefix the $i$-th mechanism is $(\varepsilon_i,\delta_i)$ edge-DP:
--   $$\Pr[\kappa_w^{(i)}(y_{<i})\in A]\le e^{\varepsilon_i}\Pr[\kappa_{w'}^{(i)}(y_{<i})\in A]+\delta_i$$
--   for all adjacent $w,w'$ and measurable $A$. Then the adaptive composition, which releases the transcript $(y_1,\dots,y_k)$, is
--   $$\Big(\sum_{i<k}\varepsilon_i,\ \sum_{i<k}\delta_i\Big)\text{ edge-DP}.$$
--   This is the step of the proof of Theorem 1 that combines the clipping release with Algorithm 1, and the outer-round composition of Lemma 18.
--
--   **Formalization Note.** Mechanisms are Markov kernels from prefixes `Fin i → Y`; `transcriptLaw` is the law of the transcript (`Def_DPCutRelease_Main_Adaptive`), and edge-DP is `IsEdgeDP` of `Def_DPCutRelease_Main_EdgeDP`.
--
--   Differences from the source:
--   - reading: "adaptively chosen randomized mechanisms, each (εᵢ, δᵢ)-differentially private" → Markov kernels κ w i on transcript prefixes, each (εᵢ, δᵢ) edge-DP at every fixed prefix; the composition is the law of the full transcript; reason: the standard meaning of adaptive composition: the mechanism chosen after any history is private
--   - encoding: Pr[M(w) ∈ A] ≤ e^ε Pr[M(w′) ∈ A] + δ for adjacent w, w′ and measurable A, and symmetrically → IsEdgeDP / IsEdgeDPFun: the inequality between real numbers (toReal) for every ordered adjacent pair; reason: adjacency is symmetric, so the swapped clause is the same condition; every law involved is a probability measure
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 11, Lemma 8

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_Adaptive

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-- Lemma 8 (Basic Adaptive Composition, p. 11): if, at every transcript prefix, the `i`-th
adaptively chosen mechanism is `(εᵢ, δᵢ)` edge-DP, the transcript of the first `k` mechanisms is
`(Σ εᵢ, Σ δᵢ)` edge-DP. -/
theorem lemma_8 {n : ℕ} {Y : Type*} [MeasurableSpace Y] (k : ℕ)
    (κ : EdgeVec n → (i : ℕ) → Kernel (Fin i → Y) Y) [∀ w i, IsMarkovKernel (κ w i)]
    (ε δ : ℕ → ℝ)
    (hDP : ∀ i < k, ∀ y : Fin i → Y, IsEdgeDP (fun w => κ w i y) (ε i) (δ i)) :
    IsEdgeDP (fun w => transcriptLaw (κ w) k) (∑ i ∈ Finset.range k, ε i)
      (∑ i ∈ Finset.range k, δ i) := by sorry

end DPCutRelease.Main
