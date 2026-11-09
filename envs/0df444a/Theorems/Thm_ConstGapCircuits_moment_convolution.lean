-- Prove2me | Theorems.Thm_ConstGapCircuits_moment_convolution
-- name    : ConstGapCircuits.moment_convolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:49.538945+00:00
-- url     : https://prove2.me/theorems/132d6cfb-8259-4ba5-b783-8f342829ad52
-- title:
--   Remark 1.14 — moment convolution and power contraction
-- statement:
--   Let $G$ be a compact Hausdorff group whose multiplication is Borel measurable, let $\nu,\nu_1,\nu_2$ be probability measures on $G$, let $\rho$ be a continuous finite-dimensional unitary representation, and let $k\ge1$. Then
--   $$M(\nu_1*\nu_2,\rho)=M(\nu_1,\rho)M(\nu_2,\rho),$$
--   $$(M(\nu,\rho)-\Pi_\rho)^k=M(\nu^{*k},\rho)-\Pi_\rho,\qquad
--   g(\nu^{*k},\rho)\le g(\nu,\rho)^k.$$
--
--   These identities express repeated-step convergence in terms of the one-step essential norm.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - generalization: finite or compact Lie groups in Definition 1.1 → compact Hausdorff groups with Borel-measurable multiplication; reason: every finite or compact Lie group in the paper has these properties
--   - encoding: convolution of probability laws → Measure.mconv with MeasurableMul₂; reason: measurability makes the product-law pushforward an actual probability law and holds for every source group
--   - reading: the k-step identity (1.17) without a printed range → positive integers k; reason: at k=0 the two sides are I and I−Π; the repeated-step formula is read for at least one step
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 7, Remark 1.14, (1.16)–(1.17)

import Definitions.Def_ConstGapCircuits_walks

namespace ConstGapCircuits

theorem moment_convolution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G]
    (ν ν₁ ν₂ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure ν]
    [MeasureTheory.IsProbabilityMeasure ν₁] [MeasureTheory.IsProbabilityMeasure ν₂]
    (ρ : UnitaryRep G) (k : ℕ) (hk : 1 ≤ k) :
    moment (ν₁.mconv ν₂) ρ = moment ν₁ ρ * moment ν₂ ρ ∧
    (moment ν ρ - invariantProjector ρ)^k =
      moment (measureProduct (List.replicate k ν)) ρ - invariantProjector ρ ∧
    essentialNorm (measureProduct (List.replicate k ν)) ρ ≤ essentialNorm ν ρ ^ k := by sorry

end ConstGapCircuits
