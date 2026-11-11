-- Prove2me | Theorems.Thm_DiffusionErrorAcc_Stability_lemma_G_2
-- name    : DiffusionErrorAcc.Stability.lemma_G_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:58:27.522755+00:00
-- url     : https://prove2.me/theorems/637491e1-26d6-402b-a55f-e2f459200eac
-- title:
--   Lemma G.2 — a continuous function orthogonal (in L²(dx)) to all of H¹(µ) vanishes
-- statement:
--   Let $\mu=\rho\,dx$ be a distribution on $\mathbb R^d$ (positive $C^1$ density, §2.3) and let $f:\mathbb R^d\to\mathbb R$ be continuous. If
--   $$\int_{\mathbb R^d}f(x)h(x)\,dx=0\qquad\text{for all }h\in H^1(\mu),$$
--   then $f$ is identically zero. This is the step of Lemma F.1 that turns the weak form of realizability back into the pointwise identity.
--
--   **Formalization Note.** The integral is a Bochner integral with respect to Lebesgue measure, so the hypothesis constrains only those $h$ for which $fh$ is integrable.
--
--   Differences from the source:
--   - encoding: µ a distribution on ℝ^d → µ = densMeasure ρ with IsRegDensity ρ (positive C¹ density); reason: §2.3 standing convention
--   - reading: H¹(µ) = {h ∈ L²(µ) : ∇h exists, and lies in L²(µ; ℝ^d)} → InH1 ρ h: h ∈ L²(µ), h differentiable on all of ℝ^d, classical gradient in L²(µ; ℝ^d); reason: '∇h exists' read as the classical gradient (the paper works with classical derivatives throughout, §2.3)
--   - generalization: ∫ f h dx = 0 for all h ∈ H¹(µ) (the integral presupposed to exist) → ∫ f h dx = 0 as a Bochner integral, which is automatic when f h is not integrable; so only h ∈ H¹(µ) with f h integrable are constrained; reason: every f satisfying the source's hypothesis satisfies the Lean one, so the Lean statement implies the source's
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 37, Lemma G.2

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_Densities

open MeasureTheory

namespace DiffusionErrorAcc.Stability

/-- Lemma G.2 (p. 37). Let `µ = ρ dx` be a distribution on `ℝ^d` (positive `C¹` density, §2.3).
Any continuous `f : ℝ^d → ℝ` with `∫_{ℝ^d} f(x) h(x) dx = 0` for all `h ∈ H¹(µ)` is identically
zero. -/
theorem lemma_G_2 {d : ℕ} (hd : 1 ≤ d) (ρ : Rd d → ℝ) (hρ : IsRegDensity ρ)
    (f : Rd d → ℝ) (hf : Continuous f)
    (horth : ∀ h : Rd d → ℝ, InH1 ρ h → ∫ x, f x * h x = 0) :
    ∀ x, f x = 0 := by sorry

end DiffusionErrorAcc.Stability
