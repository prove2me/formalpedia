-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_multiple_samples
-- name    : EFI1PRS.Uniform.multiple_samples
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:02:38.15312+00:00
-- url     : https://prove2.me/theorems/dcfc65ae-ddf8-4cce-bb08-5012e466ee99
-- title:
--   Fact 2.5 — indistinguishability of multiple samples
-- statement:
--   Let $\rho_0,\rho_1$ be normalized polynomial-qubit state families with $\rho_0\approx_c\rho_1$. For every polynomially bounded natural-valued function $t=t(\lambda)$,
--
--   $$\rho_0^{\otimes t(\lambda)}\approx_c\rho_1^{\otimes t(\lambda)}.$$
--
--   Neither efficient state generation nor computability of $t$ is required. Security continues to allow arbitrary polynomial-qubit quantum advice; the zero-copy case is the scalar tensor unit. This is independent sampling, rather than repeated outputs under a common PRS key.
--
--   Differences from the source:
--   - encoding: positive unary security parameters and ordinary finite-gate QPT circuits → zero-based wire indices, explicit finite H/S/T/X/Z/CNOT descriptions, coherent workspace and final partial traces; reason: these give explicit circuit semantics and charge all descriptions; the general simulation/compilation bridge remains a proof obligation, not a primitive assumption
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Fact 2.5, PDF/printed p. 8

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem multiple_samples {w : ℕ → ℕ}
    (ρ σ : (sec : ℕ) → Matrix (Qubits (w sec)) (Qubits (w sec)) ℂ)
    (hρ : ∀ sec, 1 ≤ sec → IsDensityMatrix (ρ sec))
    (hσ : ∀ sec, 1 ≤ sec → IsDensityMatrix (σ sec))
    (hhide : ComputationallyIndistinguishable ρ σ)
    (t : ℕ → ℕ) (ht : PolynomiallyBounded t) :
    ComputationallyIndistinguishable (fun sec => tensorSamples (ρ sec) (t sec))
      (fun sec => tensorSamples (σ sec) (t sec)) := by sorry

end EFI1PRS.Uniform
