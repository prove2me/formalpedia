-- Prove2me | Theorems.Thm_Algebra_isPrincipal_map_comap_one_div_traceDual_of_uniqueFactorizationMonoid
-- name    : Algebra.isPrincipal_map_comap_one_div_traceDual_of_uniqueFactorizationMonoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/b99c70f8-9659-586d-ad6b-7350b2dd7b6d
-- title:
--   Different becomes principal at a factorial localisation
-- statement:
--   Let $R$ be a Noetherian integrally closed domain with fraction field $K$, let $S$ be an integrally closed domain which is an $R$-algebra, finite and free as an $R$-module, and let $F$ be a field which is a fraction field of $S$ and is also a $K$-algebra and an $R$-algebra, the two scalar towers $R \to K \to F$ and $R \to S \to F$ being compatible, with $F$ separable over $K$ (all four types in a single universe). Inside $F$ form the trace dual `Submodule.traceDual R K` of the unit $S$-submodule $1 \subseteq F$, that is the $S$-submodule of those $x \in F$ for which $\operatorname{Tr}_{F/K}(xy)$ is integral over $R$ for every $y$ in the image of $S$; this is the inverse different $\mathfrak{C}_{S/R}$. Divide: $1 / \mathfrak{C}_{S/R} = \{x \in F : x\,\mathfrak{C}_{S/R} \subseteq 1\}$, and take its preimage under the $S$-linear map $S \to F$, an ideal of $S$ (the different). The assertion is that for every prime ideal $x$ of $S$ whose localisation $S_x$ is a unique factorisation monoid, the extension of this ideal to $S_x$ along $S \to S_x$ is principal.
--
--   This is the statement that the different of $S/R$, being a divisorial ideal, becomes principal after localising at a prime whose local ring is factorial. It is used in the local computation of the different that underlies [`Algebra.map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero`](thm.html#Algebra.map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero), the unramifiedness criterion in characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isPrincipal_map_comap_one_div_traceDual_of_uniqueFactorizationMonoid.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.isPrincipal_map_comap_one_div_traceDual_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (x : Ideal S) [x.IsPrime] [UniqueFactorizationMonoid (Localization.AtPrime x)] :
    (Ideal.map (algebraMap S (Localization.AtPrime x)) ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))).IsPrincipal := by sorry
