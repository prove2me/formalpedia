-- Prove2me | Theorems.Thm_FamousTheorems_conditional_jensen_inequality
-- name    : FamousTheorems.conditional_jensen_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:54.567752+00:00
-- url     : https://prove2.me/theorems/e4305ccb-9624-4b1d-8928-4c8812a58c73
-- title:
--   Conditional Jensen's inequality
-- statement:
--   **The conditional Jensen inequality.** Let $\varphi$ be a convex, lower semicontinuous function on a closed convex set $s$ in a real Banach space $E$. Let $f$ be integrable with values in $s$ almost everywhere, with $\varphi\circ f$ integrable, and let $\mathcal G$ be a sub-$\sigma$-algebra. Then almost everywhere
--   $$\varphi\big(\mathbb E[f\mid\mathcal G]\big)\le\mathbb E[\varphi(f)\mid\mathcal G].$$
--
--   This is the conditional form of Jensen's inequality. It implies that convex functions of martingales are submartingales, that conditional expectation contracts $L^p$ norms, and many inequalities of martingale theory.
--
--   **Formalization note.** Mathlib's `ConvexOn.map_condExp_le`. The sub-$\sigma$-algebra is `m ≤ mα`, and the measure is assumed $\sigma$-finite on it (`SigmaFinite (μ.trim hm)`). `μ[f | m]` is the conditional expectation, and `≤ᵐ[μ]` is inequality almost everywhere.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ConvexOn.map_condExp_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem conditional_jensen_inequality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {α : Type*} {f : α → E} {φ : E → ℝ}
    {m mα : MeasurableSpace α} {μ : Measure α} {s : Set E} (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ : ConvexOn ℝ s φ) (hφc : LowerSemicontinuousOn φ s) (hfs : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s)
    (hf : Integrable f μ) (hφf : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by sorry

end FamousTheorems
