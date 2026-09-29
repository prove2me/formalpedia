-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le
-- name    : AlgebraicGeometry.isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/5f830a79-d5e3-584f-833d-8f802dc862f2
-- title:
--   Local cutting-out by ideals implies closedness
-- statement:
--   Let $E$ be a scheme (in universe $u$) and let $T$ be a subset of the underlying topological space of $E$. Assume that for every point $e$ of $E$ there exist a type $S$ in universe $u$ with a commutative ring structure, a morphism of schemes $\iota \colon \operatorname{Spec} S \to E$ that is an open immersion, and an ideal $I$ of $S$, such that $e$ lies in the range of the continuous map $\iota$ on points, and such that for every prime ideal $\mathfrak q$ of $S$ one has $\iota(\mathfrak q) \in T$ if and only if $I \subseteq \mathfrak q$. Then $T$ is closed in $E$. Thus the hypothesis is that $T$ is traced out, on a family of affine open charts covering $E$, exactly by the zero locus of an ideal in each chart; no compatibility between the charts, and no coherence or finiteness condition on the ideals, is required.
--
--   This is the standard local criterion for closedness on a scheme, in the form in which a subset cut out in some affine open neighbourhood of each point by the vanishing of an ideal is closed. It is used to produce the closed loci attached to polarised abelian schemes, in [`AlgebraicGeometry.PolarisedAbelianScheme.exists_opens_isClosed_range_subset_iff_trace`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_opens_isClosed_range_subset_iff_trace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isClosed_of_forall_exists_isOpenImmersion_forall_mem_iff_le
    {E : Scheme.{u}} (T : Set E)
    (h : ∀ e : E, ∃ (S : Type u) (_ : CommRing S) (ι : Spec (CommRingCat.of S) ⟶ E) (_ : IsOpenImmersion ι)
        (I : Ideal S), e ∈ Set.range ι.base ∧ ∀ 𝔮 : PrimeSpectrum S, ι.base 𝔮 ∈ T ↔ I ≤ 𝔮.asIdeal) :
    IsClosed T := by sorry
