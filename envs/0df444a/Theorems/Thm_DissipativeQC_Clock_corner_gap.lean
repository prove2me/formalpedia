-- Prove2me | Theorems.Thm_DissipativeQC_Clock_corner_gap
-- name    : DissipativeQC.Clock.corner_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:09.518584+00:00
-- url     : https://prove2.me/theorems/d320287d-acea-4634-a70e-7710e44ca269
-- title:
--   Appendix p. 5 (corrected: corner −3/2, T ≥ 5) — penalized clock blocks
-- statement:
--   Start from the connected clock path matrix $P_T$ and subtract $a$ at its clock zero diagonal entry. When $a=1$, its largest eigenvalue is the value printed for the penalized block:
--
--   $$2\left(\cos\frac{\pi}{2T+3}-1\right).$$
--
--   Every real eigenvalue of this $a=1$ matrix is at most that value. For $T\ge5$ and every $a\ge\tfrac12$, every eigenvalue of the penalized matrix is strictly less than $-1/T^2$. This second assertion covers the slower one sided coherence sector and supplies the corrected bound needed by the generator.
--
--   **Formalization Note** The printed corner coefficient $-2$ corresponds to $a=1$; a one sided qubit coherence instead gives $-3/2$, or $a=1/2$. The strict bound fails for $T\le4$.
-- source:
--   Verstraete, Wolf & Cirac, Quantum computation, quantum state engineering, and quantum phase transitions driven by dissipation, arXiv:0803.1447v2, p. 5, Appendix: Efficiency of DQC, "The largest eigenvalue for the cases (ij) ≠ (00)"

import Mathlib
import Definitions.Def_DissipativeQC_Clock_Model

noncomputable section
open scoped Matrix Kronecker ComplexConjugate ComplexOrder

namespace DissipativeQC.Clock

/-- Appendix p. 5: the printed corner eigenvalue and the corrected half-penalty bound. -/
theorem corner_gap (T : ℕ) :
    (Module.End.HasEigenvalue (Matrix.toLin' (cornerMatrix T 1))
      (2 * (Real.cos (Real.pi / (2 * (T : ℝ) + 3)) - 1)) ∧
      ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (cornerMatrix T 1)) μ →
        μ ≤ 2 * (Real.cos (Real.pi / (2 * (T : ℝ) + 3)) - 1)) ∧
    (5 ≤ T → ∀ a : ℝ, (1 / 2 : ℝ) ≤ a →
      ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (cornerMatrix T a)) μ →
        μ < -1 / (T : ℝ) ^ 2) := by sorry
end DissipativeQC.Clock
