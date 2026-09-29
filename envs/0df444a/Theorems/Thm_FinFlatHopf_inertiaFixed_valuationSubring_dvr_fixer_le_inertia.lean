-- Prove2me | Theorems.Thm_FinFlatHopf_inertiaFixed_valuationSubring_dvr_fixer_le_inertia
-- name    : FinFlatHopf.inertiaFixed_valuationSubring_dvr_fixer_le_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/c2f4a811-a3f3-54c9-94b7-4271e91df38f
-- title:
--   Inertia-fixed subring of a place over p: uniformiser p
-- statement:
--   Let $p$ be a prime, let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$, meaning that the image of $p$ in $\overline{\mathbb{Q}}$ is a nonunit of $P$, and let $B$ be a subring of $\overline{\mathbb{Q}}$ whose elements are characterised by: $x \in B$ if and only if $x \in P$ and $\sigma x = x$ for every $\sigma$ in `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $P$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup. Then three assertions hold. First, the image of $p$ in $B$ is a nonunit of $B$, and every nonzero $x \in B$ can be written $x = u \cdot p^{k}$ with $k \in \mathbb{N}$ and $u$ a unit of $B$; thus $p$ plays the role of a uniformiser. Second, for every rational $q$ whose denominator is coprime to $p$, the image of $q$ in $\overline{\mathbb{Q}}$ lies in $B$, i.e. $B$ contains $\mathbb{Z}_{(p)}$. Third, every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ fixing $B$ pointwise belongs to `P.inertiaSubgroupIn ℚ`, so the pointwise fixer of $B$ is exactly the inertia subgroup.
--
--   This identifies the inertia-fixed part of a place of $\overline{\mathbb{Q}}$ above $p$ as a valuation ring of discrete type with uniformiser $p$ containing $\mathbb{Z}_{(p)}$, and recovers the inertia subgroup as its pointwise stabiliser — the ring-theoretic form of the statement that the inertia field is the maximal unramified subextension. It is used in the construction of subgroups with trivial inertia quotient on cyclotomic extensions and in the prolongation of place specialisations along node coordinates of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FinFlatHopf_inertiaFixed_valuationSubring_dvr_fixer_le_inertia.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FinFlatHopf.inertiaFixed_valuationSubring_dvr_fixer_le_inertia (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (B : Subring (AlgebraicClosure ℚ))
    (hB : ∀ x : AlgebraicClosure ℚ, x ∈ B ↔
      (x ∈ P ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x)) :
    ((p : B) ∈ nonunits B ∧ ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : Bˣ), x = u * (p : B) ^ k) ∧
    (∀ q : ℚ, q ∈ GaloisRep.ratLocalizedAt p → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ B) ∧
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ B, σ x = x) →
      σ ∈ P.inertiaSubgroupIn ℚ) := by sorry
