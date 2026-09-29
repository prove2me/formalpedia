-- Prove2me | Theorems.Thm_ChatterjeeQFT_massShell_lorentz_invariant
-- name    : ChatterjeeQFT.massShell_lorentz_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:27:04.372347+00:00
-- url     : https://prove2.me/theorems/55d978bf-2336-4b02-80aa-be1d46ebee34
-- title:
--   The mass shell is invariant under $SO^{\uparrow}(1,3)$
-- statement:
--   If $L$ belongs to the restricted Lorentz group $SO^{\uparrow}(1,3)$ — that is, $L$
--   preserves the Minkowski inner product, $\det L = 1$ and $L^0{}_0 > 0$ — then $L$ maps the mass
--   shell into itself:
--
--   $$p \in X_m \;\Longrightarrow\; Lp \in X_m .$$
--
--   Preservation of the quadratic condition $p^2 = m^2$ is immediate from Lorentz invariance; the
--   content of the statement is that the orthochronous condition $L^0{}_0 > 0$ forces the energy of
--   $Lp$ to stay nonnegative, i.e. that $SO^{\uparrow}(1,3)$ preserves the closed forward cone. This
--   is the action of $SO^{\uparrow}(1,3)$ on $X_m$ whose invariant measure is constructed in Lecture
--   10.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 9 §9.2 and §9.5, pp. 38 and 40; Lecture 10 §10.1, p. 41 (the restricted Lorentz group acts on $X_m$).

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
open MeasureTheory Matrix
open scoped ENNReal

namespace ChatterjeeQFT

theorem massShell_lorentz_invariant (m : ℝ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsRestrictedLorentz L) (p : Fin 4 → ℝ) (hp : p ∈ massShell m) :
    L *ᵥ p ∈ massShell m := by sorry

end ChatterjeeQFT
