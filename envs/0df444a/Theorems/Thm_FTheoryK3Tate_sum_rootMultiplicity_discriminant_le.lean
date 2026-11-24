-- Prove2me | Theorems.Thm_FTheoryK3Tate_sum_rootMultiplicity_discriminant_le
-- name    : FTheoryK3Tate.sum_rootMultiplicity_discriminant_le
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T08:55:33.509172+00:00
-- url     : https://prove2.me/theorems/1187162f-476b-4047-aece-0b7058e42b99
-- title:
--   Milestone 2 — local orders bounded by $\deg\Delta$
-- statement:
--   Let $k$ be a field, $f, g \in k[X]$ with $\Delta = 4f^3 + 27g^2 \ne 0$. For every finite set $S \subseteq k$ of base points, $\sum_{t_0 \in S} \operatorname{ord}_{t_0}(\Delta) \le \deg \Delta$: the degenerate fibres over $S$, counted with multiplicity, are bounded by the degree of the discriminant. Points of $S$ that are not roots contribute $0$; the elements of the `Finset` $S$ are distinct.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: J. Tate, "Algorithm for determining the type of a singular fiber in an elliptic pencil" (Modular Functions of One Variable IV, LNM 476, 1975); M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras (up to E8) and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k]
/-- Milestone (local orders bounded by the discriminant degree). For `Δ ≠ 0` and any finite
    set `S` of base points, the discriminant orders at the points of `S`, summed with
    multiplicity, are bounded by `deg Δ`. -/
theorem sum_rootMultiplicity_discriminant_le (f g : k[X]) (h : Δ f g ≠ 0) (S : Finset k) :
    (∑ t₀ ∈ S, (Δ f g).rootMultiplicity t₀) ≤ (Δ f g).natDegree := by
  sorry
end FTheoryK3Tate
