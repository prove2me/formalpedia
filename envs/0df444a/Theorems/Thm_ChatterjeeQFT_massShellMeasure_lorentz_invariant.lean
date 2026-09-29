-- Prove2me | Theorems.Thm_ChatterjeeQFT_massShellMeasure_lorentz_invariant
-- name    : ChatterjeeQFT.massShellMeasure_lorentz_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:30:31.11432+00:00
-- url     : https://prove2.me/theorems/1c0484f7-9905-4413-a7ea-2450d2792046
-- title:
--   Lorentz invariance of $\lambda_m$
-- statement:
--   The measure $\lambda_m$ constructed from equation (10.1) is invariant under the
--   restricted Lorentz group: for every $L \in SO^{\uparrow}(1,3)$, the push-forward of $\lambda_m$
--   under $p \mapsto Lp$ is again $\lambda_m$. Equivalently, for every integrable $f$,
--
--   $$\int_{X_m} f(Lp)\, d\lambda_m(p) \;=\; \int_{X_m} f(p)\, d\lambda_m(p).$$
--
--   This is the property that motivates the whole construction of §10.2, and it is used silently in
--   Lecture 25 when the unitarity of the electron representation is proved ("by the Lorentz
--   invariance of $d\lambda_m$").
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 10 §10.1-§10.2, pp. 41-42 ($\lambda_m$ is invariant under the action of the restricted Lorentz group); used in Lecture 25 §25.3, p. 109.

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
open MeasureTheory Matrix
open scoped ENNReal

namespace ChatterjeeQFT

theorem massShellMeasure_lorentz_invariant (m : ℝ) (hm : 0 < m)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsRestrictedLorentz L) :
    Measure.map (fun p : Fin 4 → ℝ => L *ᵥ p) (massShellMeasure m) = massShellMeasure m := by
  sorry

end ChatterjeeQFT
