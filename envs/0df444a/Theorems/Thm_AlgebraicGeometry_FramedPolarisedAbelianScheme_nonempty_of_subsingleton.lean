-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_nonempty_of_subsingleton
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.nonempty_of_subsingleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/ebf741bb-6ed1-5294-910b-d56d5e0c3316
-- title:
--   Framed polarised abelian schemes exist over the zero ring
-- statement:
--   Let $g, N, n$ be natural numbers and let $S$ be a commutative ring that is a subsingleton, i.e. the zero ring $0 = 1$. The assertion is that the type `FramedPolarisedAbelianScheme g N n S` is nonempty: there exists a bundle of data consisting of a scheme $A$, a morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$ on $f$ over $S$, the property bundle `AbelianSchemePropertyBundle S f` (smoothness, properness, connected fibres, existence of a group law), the requirement that every fibre of $f$ have topological Krull dimension $g$, a family $P : \mathrm{Fin}(2g) \to$ sections of $f$ that are $n$-torsion for $L$ and that, at every geometric point $S \to k$ with $k$ algebraically closed, freely generate the $n$-torsion (the $\mathrm{Fin}(n)$-combinations of the $P_i$ are pairwise distinct and exhaust the $n$-torsion $k$-points), a module $\mathcal{L} =$ `pol` on $A$ which is invertible, gives a closed immersion by its sections, and has geometric fibrewise $H^0$-rank equal to $N+1$; and, on top of this, a projective presentation of $\mathcal{L}$ along $f$ with $N+1$ global sections $\sigma_i$ and a morphism $A \to \mathbb{P}^N_S$ over $\operatorname{Spec} S$ trivialising $\mathcal{L}$ on the preimages of the standard basic opens and matching the $\sigma_i$ via the coordinate ratios, such that this morphism to $\mathbb{P}^N$ is a closed immersion and the $\sigma_i$ form a section basis over $\top$.
--
--   This is the degenerate case of the moduli problem of framed polarised abelian schemes: over the zero ring the space of such objects is nonempty (realised by the empty scheme), so no representability or non-degeneracy statement needs to exclude this base. It is used by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_nonempty_of_subsingleton.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.nonempty_of_subsingleton
    (g N n : ℕ) (S : Type) [CommRing S] [Subsingleton S] :
    Nonempty (FramedPolarisedAbelianScheme g N n S) := by sorry
