-- Prove2me | Theorems.Thm_DissipativeQC_Clock_path_gap
-- name    : DissipativeQC.Clock.path_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:35:10.967824+00:00
-- url     : https://prove2.me/theorems/3352b4c5-937e-4770-88ea-9b78e38828f8
-- title:
--   Appendix p. 5 — first nonzero eigenvalue of the connected L₀₀ clock path
-- statement:
--   Let $P_T$ be the real symmetric generator of a path on clock times $0,\ldots,T$: neighboring entries are $1$ and each diagonal entry is minus the vertex degree. For $T\ge1$, zero is an eigenvalue and the largest nonzero eigenvalue is
--
--   $$2\left(\cos\frac{\pi}{T+1}-1\right).$$
--
--   Every other nonzero real eigenvalue is no larger than this value. This identifies the relaxation scale of the unpenalized clock sector.
--
--   **Formalization Note** The path uses the first edge $0\leftrightarrow1$, which the displayed sum on p. 5 omits even though the paper's stated eigenvalue requires it.
-- source:
--   Verstraete, Wolf & Cirac, Quantum computation, quantum state engineering, and quantum phase transitions driven by dissipation, arXiv:0803.1447v2, p. 5, Appendix: Efficiency of DQC, "The gap of L00 can be calculated exactly"

import Mathlib
import Definitions.Def_DissipativeQC_Clock_Model

noncomputable section
open scoped Matrix Kronecker ComplexConjugate ComplexOrder

namespace DissipativeQC.Clock

/-- Appendix p. 5: the first nonzero eigenvalue of the connected L_00 block. -/
theorem path_gap (T : ℕ) (hT : 1 ≤ T) :
    Module.End.HasEigenvalue (Matrix.toLin' (pathMatrix T)) 0 ∧
    Module.End.HasEigenvalue (Matrix.toLin' (pathMatrix T))
      (2 * (Real.cos (Real.pi / ((T : ℝ) + 1)) - 1)) ∧
    ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (pathMatrix T)) μ → μ ≠ 0 →
      μ ≤ 2 * (Real.cos (Real.pi / ((T : ℝ) + 1)) - 1) := by sorry
end DissipativeQC.Clock
