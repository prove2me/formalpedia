-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing
-- name    : Deformation.DieudonneModule.exists_frobenius_iterate_eq_zero_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/10360dc3-d656-5aab-8e80-aa2019534fc4
-- title:
--   Frobenius is nilpotent on the Dieudonné module of a local bialgebra
-- statement:
--   Let $p$ be a prime, and let $B$ be a commutative ring carrying a bialgebra structure over $\mathbb{Z}/p$ which is finite as a $\mathbb{Z}/p$-module, and assume that $B$ is a local ring. For each $k$, [`Deformation.wittHom (ZMod p) p k B`](def/Dieudonne_WittVectorHom.html#L246) is the additive subgroup of the truncated Witt vectors $W_k(B)$ of length $k$ consisting of those $x$ with $W_k(\Delta)(x) = W_k(\iota_1)(x) + W_k(\iota_2)(x)$, where $\Delta\colon B \to B \otimes_{\mathbb{Z}/p} B$ is the comultiplication and $\iota_1,\iota_2$ are the two inclusions of $B$ into $B \otimes_{\mathbb{Z}/p} B$; the module [`Deformation.DieudonneModule (ZMod p) p B`](def/Dieudonne_WittHomColimit.html#L234) is the direct limit of these groups along the length-raising shift maps [`Deformation.wittHomShiftLE`](def/Dieudonne_WittHomColimit.html#L168), and [`Deformation.DieudonneModule.frobenius (ZMod p) p B`](def/Dieudonne_WittHomColimit.html#L333) is the additive endomorphism of the limit induced by the maps [`Deformation.wittHomFrobenius`](def/Dieudonne_WittVectorHom.html#L391), which act on each level by the Witt-vector Frobenius `TruncWitt.frobeniusFun`. The assertion is that there exists a natural number $n$, uniform in the element, such that the $n$-fold iterate of this Frobenius endomorphism sends every element $z$ of the Dieudonné module to $0$.
--
--   In classical terms, for a finite commutative group (indeed monoid) scheme $G = \operatorname{Spec} B$ over $\mathbb{F}_p$ with connected (i.e. local) coordinate ring, Frobenius is nilpotent on the contravariant Dieudonné module $\varinjlim_k \operatorname{Hom}(G, W_k)$; no cocommutativity hypothesis enters. It is used in the theory of Honda systems, being cited by [`Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct`](thm.html#Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v

theorem Deformation.DieudonneModule.exists_frobenius_iterate_eq_zero_of_isLocalRing
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [Bialgebra (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsLocalRing B) :
    ∃ n : ℕ, ∀ z : Deformation.DieudonneModule (ZMod p) p B,
      (Deformation.DieudonneModule.frobenius (ZMod p) p B)^[n] z = 0 := by sorry
