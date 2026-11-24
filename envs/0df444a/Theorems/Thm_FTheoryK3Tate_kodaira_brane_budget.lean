-- Prove2me | Theorems.Thm_FTheoryK3Tate_kodaira_brane_budget
-- name    : FTheoryK3Tate.kodaira_brane_budget
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T09:00:27.859897+00:00
-- url     : https://prove2.me/theorems/7d58e077-0447-45ab-87d6-014707f62fa0
-- title:
--   Goal — the Kodaira/Tate 7-brane budget $\sum \operatorname{discOrder} \le 24$
-- statement:
--   Let $k$ be a field of characteristic zero and $f, g \in k[X]$ satisfy the Calabi--Yau/K3 degree data $\deg f \le 8$, $\deg g \le 12$, $\Delta = 4f^3 + 27g^2 \ne 0$. Let $S \subseteq k$ be any finite set of base points and $\tau$ an assignment of a reduced Kodaira/Tate type to each, such that the fibre at every $t \in S$ genuinely has type $\tau(t)$ (`HasKodaira f g t (τ t)`). Then the total discriminant charge of these fibres is bounded by the degree of the discriminant:
--   $$\sum_{t \in S} \operatorname{discOrder}(\tau(t)) \le 24.$$
--   This is the F-theory **7-brane budget**: each classified fibre contributes its Tate-table discriminant order, and the sum over any collection of distinct classified fibres cannot exceed $\deg\Delta \le 24$. It bounds the maximal non-abelian enhancement of an elliptic K3 (e.g. at most two $E_8$ or $E_7$ points, at most three $E_6$ points). **Scope note.** The statement is an upper bound over the fibres one chooses to classify; it does not assert that $S$ exhausts the singular locus, nor that $\tau(t)$ is the unique type at $t$.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: J. Tate, "Algorithm for determining the type of a singular fiber in an elliptic pencil" (Modular Functions of One Variable IV, LNM 476, 1975); M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras (up to E8) and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k] [CharZero k]
/-- **Goal — the Kodaira/Tate 7-brane budget.** For a Calabi–Yau/K3 Weierstrass model, take
    any finite set `S` of base points together with an assignment `τ` giving each point of `S`
    a reduced Kodaira/Tate type it actually carries (`HasKodaira f g t (τ t)`). Then the total
    discriminant charge of those fibres, `∑_{t ∈ S} (τ t).discOrder`, is at most `24`.

    Every entry of the Tate table is load-bearing here: each `discOrder` is converted to the
    actual `ord_{t} Δ` by the corresponding per-type milestone, and the sum of local orders is
    bounded by `deg Δ ≤ 24`. As corollaries, at most two `E₈` (II*) or `E₇` (III*) points, at
    most three `E₆` (IV*) points, and the `E₈ × E₈` maximal-enhancement bound. -/
theorem kodaira_brane_budget (f g : k[X]) (h : IsK3Data f g)
    (S : Finset k) (τ : k → Kodaira)
    (hτ : ∀ t ∈ S, HasKodaira f g t (τ t)) :
    ∑ t ∈ S, (τ t).discOrder ≤ 24 := by
  sorry
end FTheoryK3Tate
