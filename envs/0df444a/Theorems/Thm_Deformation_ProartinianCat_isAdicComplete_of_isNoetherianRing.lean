-- Prove2me | Theorems.Thm_Deformation_ProartinianCat_isAdicComplete_of_isNoetherianRing
-- name    : Deformation.ProartinianCat.isAdicComplete_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/0042369d-8cdd-5eac-9c5a-6e78eeac059f
-- title:
--   Noetherian pro-Artinian algebras are 𝔪-adically complete
-- statement:
--   Let $\mathcal O$ be a commutative ring in universe $u$ which is local and whose residue field $\mathcal O/\mathfrak m_{\mathcal O}$ is finite, and let $R$ be an object of [`Deformation.ProartinianCat 𝓞`](def/Deformations_ProartinianCat.html#L44), that is, a type in universe $u$ carrying a commutative ring structure, a topology and an $\mathcal O$-algebra structure such that `IsLocalProartinianAlgebra 𝓞 R` holds: $R$ is a topological ring, a local ring, satisfies [`IsProartinian`](def/Deformations_IsProartinian.html#L185), the structure morphism $\mathcal O \to R$ is a local homomorphism, and $R$ is a residue algebra over $\mathcal O$ (so the induced map on residue fields is bijective). Assume in addition that the ring $R$ is Noetherian. The conclusion is `IsAdicComplete (maximalIdeal R) R`: $R$ is Hausdorff and precomplete for the filtration by the powers $\mathfrak m_R^n$ of its maximal ideal, i.e. $\bigcap_n \mathfrak m_R^n = 0$ and every sequence in $R$ that is Cauchy for this filtration converges, so that the canonical map $R \to \varprojlim_n R/\mathfrak m_R^n$ is an isomorphism. Note that this conclusion is the purely algebraic notion of adic completeness, stated for the ideal $\mathfrak m_R$ and not for the given topology on $R$.
--
--   This is the standard fact that a Noetherian local pro-Artinian algebra over a base with finite residue field is complete and separated for its maximal ideal, as used in the deformation theory of Galois representations. It supplies the completeness requirement for the carrier of the deformation ring data in [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_ProartinianCat_isAdicComplete_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_Deformations_ProartinianCat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

universe u

theorem Deformation.ProartinianCat.isAdicComplete_of_isNoetherianRing
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (ResidueField 𝓞)]
    (R : Deformation.ProartinianCat 𝓞) [IsNoetherianRing R] :
    IsAdicComplete (maximalIdeal R) R := by sorry
