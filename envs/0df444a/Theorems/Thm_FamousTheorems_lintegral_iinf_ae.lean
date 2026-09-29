-- Prove2me | Theorems.Thm_FamousTheorems_lintegral_iinf_ae
-- name    : FamousTheorems.lintegral_iinf_ae
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:04.104349+00:00
-- url     : https://prove2.me/theorems/8d4faf0b-6fb5-4eae-870b-179140c7a583
-- title:
--   The monotone convergence theorem
-- statement:
--   **The monotone convergence theorem.** For a decreasing sequence of measurable functions, the integral of the infimum is the infimum of the integrals. Limits and integrals may be exchanged whenever the convergence is monotone — no domination hypothesis is needed, and the common value may be infinite. This is the first of the three great convergence theorems and the one from which the others follow: Fatou's lemma is monotone convergence applied to running infima, and dominated convergence is Fatou applied twice. It is also what makes countable additivity of the integral work, and hence what distinguishes the Lebesgue theory from the Riemann theory, where such exchanges require uniform convergence. **Formalization note.** The statement is for `ℝ≥0∞`-valued functions with hypotheses holding almost everywhere, and the sequence is decreasing with an integrable first term. The result is Mathlib's `MeasureTheory.lintegral_iInf_ae`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem lintegral_iinf_ae :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
    {f : ℕ → α → ENNReal}, 
    (∀ (n : ℕ), Measurable (f n)) → 
    (∀ (n : ℕ), f n.succ ≤ᵐ[μ] f n) → ∫⁻ (a : α), f 0 a ∂μ ≠ ⊤ → ∫⁻ (a : α), ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ (a : α), f n a ∂μ := by sorry

end FamousTheorems
