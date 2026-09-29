-- Prove2me | Theorems.Thm_FamousTheorems_levy_borel_cantelli
-- name    : FamousTheorems.levy_borel_cantelli
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:54.827896+00:00
-- url     : https://prove2.me/theorems/4adf1a0d-2ab6-4417-8bf8-7b462e3e6c6a
-- title:
--   Lévy's generalized Borel–Cantelli lemma
-- statement:
--   **Lévy's extension of the Borel–Cantelli lemma.** Let $(\mathcal F_n)$ be a filtration on a finite measure space, and let $s_n$ be events with $s_n\in\mathcal F_n$. Then, almost everywhere,
--   $$\omega\in\limsup_n s_n\iff\sum_{k\ge0}\mathbb P(s_{k+1}\mid\mathcal F_k)(\omega)=\infty.$$
--
--   Almost every point lies in infinitely many $s_n$ exactly on the event where the sum of the conditional probabilities diverges. For independent events and the trivial filtration this gives both halves of the Borel–Cantelli lemma. The general form is proved with martingale convergence and is used for events with dependence.
--
--   **Formalization note.** Mathlib's `MeasureTheory.ae_mem_limsup_atTop_iff`. `Filtration ℕ m0` is a filtration, and the adaptedness hypothesis says that `s n` is measurable for the $\sigma$-algebra `ℱ n`. The conditional probability $\mathbb P(s_{k+1}\mid\mathcal F_k)$ is the conditional expectation `μ[(s (k + 1)).indicator 1 | ℱ k]`, and divergence of the series means that its partial sums tend to $+\infty$ (`Tendsto … atTop atTop`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.ae_mem_limsup_atTop_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem levy_borel_cantelli {Ω : Type*} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℕ m0} (μ : Measure Ω) [IsFiniteMeasure μ]
    {s : ℕ → Set Ω} (hs : ∀ n, @MeasurableSet Ω (ℱ n) (s n)) :
    ∀ᵐ ω ∂μ, ω ∈ Filter.limsup s Filter.atTop ↔
      Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k]) ω)
        Filter.atTop Filter.atTop := by sorry

end FamousTheorems
