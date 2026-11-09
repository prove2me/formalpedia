-- Prove2me | Theorems.Thm_ConstGapCircuits_detectability
-- name    : ConstGapCircuits.detectability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:34.006414+00:00
-- url     : https://prove2.me/theorems/e2a7908d-de31-4ab4-a72b-5093c65c6ed8
-- title:
--   Lemma 1.24 — detectability and Gao converse
-- statement:
--   Let $H_1,\ldots,H_L$ be an indexed family of compact subgroups of a compact Hausdorff group $G$, with $L\ge1$. Suppose each $H_i$ commutes elementwise with all but at most $\ell$ other indices, where $\ell\ge1$. Repeated subgroups retain their multiplicity. Let $\Sigma=L^{-1}\sum_i\mu_{H_i}$ and $\star=\mu_{H_1}*\cdots*\mu_{H_L}$. For every continuous finite-dimensional unitary representation $\rho$,
--   $$\Delta(\Sigma,\rho)\ge\frac1{4L}\Delta(\star,\rho),\qquad
--   \Delta(\star,\rho)\ge\frac14\min\{1,L\ell^{-2}\Delta(\Sigma,\rho)\}.$$
--
--   Both directions of comparison are retained. They compare averaged local gates with a sequential layer of those gates.
--
--   **Formalization Note** The statement expands the two moment operators to the sum and ordered product of the subgroup projectors. This also treats compact groups without a second-countability assumption.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - reading: each subgroup commutes with all but ℓ others → at most ℓ noncommuting other indices; reason: the uses at the ends of a chain and at L=1 require an upper bound rather than equality
--   - encoding: compact subgroups and the gaps of their average and convolution → closed subgroups and the gaps computed from the average and product of Haar projectors; reason: compact subgroups are closed in a Hausdorff group; (1.16) identifies the convolution moment with this product, so no gap or multiplicity changes
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 8, Lemma 1.24, (1.25)–(1.26)

import Definitions.Def_ConstGapCircuits_walks

namespace ConstGapCircuits
attribute [local instance] Classical.propDecidable

theorem detectability {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (L ℓ : ℕ) (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ) (H : Fin L → ClosedSubgroup G)
    (hcomm : ∀ i : Fin L, (Finset.univ.filter (fun j : Fin L =>
      j ≠ i ∧ ¬ (∀ a : H i, ∀ b : H j, (a : G) * b = (b : G) * a))).card ≤ ℓ)
    (ρ : UnitaryRep G) :
    (1 - opNorm ((L : ℂ)⁻¹ • (∑ j, subgroupProjector (H j) ρ) - invariantProjector ρ)) ≥
      (1 / (4 * (L : ℝ))) * (1 - opNorm
        ((((List.finRange L).map (fun j => subgroupProjector (H j) ρ)).prod) - invariantProjector ρ)) ∧
    (1 - opNorm ((((List.finRange L).map (fun j => subgroupProjector (H j) ρ)).prod) - invariantProjector ρ)) ≥
      (1 / 4 : ℝ) * min 1 ((L : ℝ) / (ℓ : ℝ)^2 *
        (1 - opNorm ((L : ℂ)⁻¹ • (∑ j, subgroupProjector (H j) ρ) - invariantProjector ρ))) := by sorry

end ConstGapCircuits
