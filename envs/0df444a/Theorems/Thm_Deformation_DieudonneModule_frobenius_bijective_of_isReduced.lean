-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_frobenius_bijective_of_isReduced
-- name    : Deformation.DieudonneModule.frobenius_bijective_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/e3aeb6cf-cb17-526b-b2f8-6731b006273d
-- title:
--   Frobenius is bijective on the Dieudonné module of a reduced bialgebra
-- statement:
--   Let $p$ be a prime and let $B$ be a commutative ring carrying the structure of a bialgebra over $\mathbb{Z}/p$ which is finite as a $\mathbb{Z}/p$-module, and assume $B$ is reduced. The assertion is that the additive endomorphism [`Deformation.DieudonneModule.frobenius (ZMod p) p B`](def/Dieudonne_WittHomColimit.html#L333) is bijective as a function. Here `DieudonneModule (ZMod p) p B` is the direct limit, over $n$, of the additive groups `wittHom (ZMod p) p n B` of those truncated Witt vectors $x \in W_n(B)$ which are primitive in the sense that the functorial image of $x$ under the comultiplication $B \to B \otimes_{\mathbb{Z}/p} B$ equals the sum of its images under the two inclusions $B \to B \otimes_{\mathbb{Z}/p} B$, the transition maps being the additive maps induced by the Witt-vector shift `TruncWitt.shiftLE` for $n \le m$; and `frobenius` is the additive endomorphism of this limit induced on each level by the Witt-vector Frobenius `TruncWitt.frobeniusFun` restricted to the subgroup of primitive elements, these levelwise maps being compatible with the shifts.
--
--   In the classical dictionary this is the statement that the Frobenius operator on the (contravariant) Dieudonné module $M(G) = \varinjlim_n \operatorname{Hom}(G, W_n)$ of a finite commutative group scheme $G = \operatorname{Spec} B$ over $\mathbb{F}_p$ is bijective when $G$ is étale, i.e. when $B$ is reduced. It is used in the Honda-system part of the deformation-theoretic input, where it serves to split off the étale part: it is cited by [`Deformation.HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq`](thm.html#Deformation.HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq) and [`Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct`](thm.html#Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v

theorem Deformation.DieudonneModule.frobenius_bijective_of_isReduced
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [Bialgebra (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsReduced B) :
    Function.Bijective (Deformation.DieudonneModule.frobenius (ZMod p) p B) := by sorry
