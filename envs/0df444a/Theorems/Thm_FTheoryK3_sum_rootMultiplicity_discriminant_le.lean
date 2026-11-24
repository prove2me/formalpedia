-- Prove2me | Theorems.Thm_FTheoryK3_sum_rootMultiplicity_discriminant_le
-- name    : FTheoryK3.sum_rootMultiplicity_discriminant_le
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-21T20:00:56.12128+00:00
-- url     : https://prove2.me/theorems/479a73f4-f107-4341-b65d-92faabeda6c9
-- title:
--   Branes with multiplicity are bounded by $\deg\Delta$
-- statement:
--   Let $k$ be a field and $f, g \in k[X]$ with $\Delta = 4f^3 + 27g^2 \ne 0$. For every finite set $S \subseteq k$ of base points, $$\sum_{t_0 \in S} \operatorname{ord}_{t_0}(\Delta) \;\le\; \deg \Delta.$$
--
--   The left-hand side counts, with multiplicity, the degenerate fibres (7-branes) at the points of $S$; the inequality says the total brane charge over any finite collection of points is bounded by the degree of the discriminant. Points of $S$ that are not roots of $\Delta$ contribute $0$.
--
--   **Formalization Note.** The hypothesis $\Delta \ne 0$ is needed for $\deg\Delta$ (`natDegree`) to be a meaningful bound; the sum ranges over a `Finset`, whose elements are distinct.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number of an elliptic surface = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24 singular fibres). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras up to E8, and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3Core
open Polynomial
variable {k : Type*} [Field k]

namespace FTheoryK3
theorem sum_rootMultiplicity_discriminant_le
    (f g : k[X]) (h : Δ f g ≠ 0) (S : Finset k) :
    (∑ t₀ ∈ S, (Δ f g).rootMultiplicity t₀) ≤ (Δ f g).natDegree := by
  sorry
end FTheoryK3
