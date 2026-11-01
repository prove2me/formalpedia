-- Prove2me | Theorems.Thm_AssignToSeatRM_theorem_2_strongly_nse_iff
-- name    : AssignToSeatRM.theorem_2_strongly_nse_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:59.63479+00:00
-- url     : https://prove2.me/theorems/afbb9c3e-f68a-4959-97c3-9688e8005eaf
-- title:
--   Theorem 2 (first sentence) — the IP (1) equals the aggregated LP (3) for all integer demands iff $C$ is strongly NSE
-- statement:
--   Let $C\in\{0,1\}^{N\times M}$ be a capacity matrix and let the prices be positive, $p_{ij}>0$ for every itinerary $1\le i\le j\le M$. Then
--
--   $$\mathrm{IP}(1)(C,p,d)=\mathrm{LP}(3)(C,p,d)\quad\text{for every } d\in\mathbb N^{\{i\le j\}}\qquad\Longleftrightarrow\qquad C \text{ is strongly NSE}.$$
--
--   Here (1) is the seat-level allocation problem with the assign-to-seat restriction and (3) the aggregated problem that only respects the number $c_\ell$ of free seats on each leg. Strongly NSE (Definition 2) means that any two maximal sequences of free legs in $C$ share an endpoint or are separated by at least one leg.
--
--   The theorem says exactly when the assign-to-seat restriction costs nothing in the static problem; the "if" direction is used in the proof of Lemma 1.
--
--   **Formalization Note** Optimal values are suprema of the objective over the feasible sets. The second sentence of Theorem 2 (polynomial-time solvability for NSE matrices) is not part of this item.
--
--   Differences from the source:
--   - encoding: legs 1..M, itineraries i ≤ j, C ∈ {0,1}^{N×M} with C_{k0} = C_{k(M+1)} = 0 → natural-number indices with explicit bounds (itins M); C : Fin N → Fin M → Bool read through cap, which is false outside 1..M; reason: Lean convention; same instances
--   - encoding: the optimal value of a linear program → sSup of the objective over the feasible set; reason: the feasible sets that occur are nonempty and bounded, so the sSup is the maximum; same values
--   - encoding: x_{k,ij} ∈ {0,1} → real x_{k,ij} with x_{k,ij} = 0 ∨ x_{k,ij} = 1; reason: same feasible points
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, Theorem 2 (first sentence), p.12; Definition 2, p.11

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_StaticLP

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Theorem 2, first sentence** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188, p.12): for any fixed positive prices `{p_{ij}}`, the IP (1) and the
aggregated LP (3) have the same optimal value for any nonnegative integer demands `{d_{ij}}` if
and only if `C` is strongly NSE (Definition 2, p.11).

**Formalization Note.** `C : CapMat N M` with legs `1, …, M` and padding `C_{k0} = C_{k(M+1)} = 0`;
prices are positive on every itinerary `1 ≤ i ≤ j ≤ M`; demands are `d : ℕ → ℕ → ℕ`. Both optimal
values are `sSup`s of nonempty bounded sets of reals. The second sentence of Theorem 2
(polynomial-time solvability for NSE `C`) is not formalized. -/
theorem theorem_2_strongly_nse_iff {N M : ℕ} (C : CapMat N M) (p : ℕ → ℕ → ℝ)
    (hp : ∀ ij ∈ itins M, 0 < p ij.1 ij.2) :
    (∀ d : ℕ → ℕ → ℕ, ip1Value C p d = lp3Value C p (fun i j => (d i j : ℝ))) ↔
      IsStronglyNSE C := by sorry

end AssignToSeatRM
