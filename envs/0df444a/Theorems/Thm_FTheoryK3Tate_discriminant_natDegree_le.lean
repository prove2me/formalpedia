-- Prove2me | Theorems.Thm_FTheoryK3Tate_discriminant_natDegree_le
-- name    : FTheoryK3Tate.discriminant_natDegree_le
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T08:54:21.359887+00:00
-- url     : https://prove2.me/theorems/244336f5-3800-40d8-9831-4c7168646b93
-- title:
--   Milestone 1 — $\deg\Delta \le 24$ (24 seven-branes)
-- statement:
--   Let $k$ be a field and $f, g \in k[X]$. If $\deg f \le 8$ and $\deg g \le 12$, then the discriminant $\Delta = 4f^3 + 27g^2$ satisfies $\deg \Delta \le 24$. This is the 7-brane count $\deg\Delta = \chi(\mathrm{K3}) = 24$ (with multiplicity). **Formalization note.** Degrees are `natDegree` (zero polynomial has degree $0$), so the bound holds trivially if $\Delta = 0$; no characteristic hypothesis is needed.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: J. Tate, "Algorithm for determining the type of a singular fiber in an elliptic pencil" (Modular Functions of One Variable IV, LNM 476, 1975); M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras (up to E8) and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k]
/-- Milestone (24 seven-branes). Under the Calabi–Yau degree bound `deg f ≤ 8`, `deg g ≤ 12`,
    the discriminant `Δ = 4f³ + 27g²` has degree at most `24`. -/
theorem discriminant_natDegree_le (f g : k[X])
    (hf : f.natDegree ≤ 8) (hg : g.natDegree ≤ 12) :
    (Δ f g).natDegree ≤ 24 := by
  sorry
end FTheoryK3Tate
