-- Prove2me | Theorems.Thm_CuspidalType_torus_unitsMap_algebraMap
-- name    : CuspidalType.torus_unitsMap_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/08a70d92-b8ec-5bf7-8952-365e1f8d25bc
-- title:
--   Torus image of a prime-field unit is scalar
-- statement:
--   Let $q$ be a natural number assumed prime (via a `Fact` instance), and let $c$ be a unit of $\mathbb{Z}/q$. Two homomorphisms into the group `GL2 q` of invertible $2\times 2$ matrices over $\mathbb{Z}/q$ are involved. First, `scalarElem q` is the monoid homomorphism $(\mathbb{Z}/q)^\times \to$ `GL2 q` obtained by applying `Units.map` to the ring homomorphism $\mathrm{Matrix.scalar}$, so that $c$ is sent to the diagonal matrix with both diagonal entries equal to $c$. Second, `torus q` is the monoid homomorphism $(\mathrm{GaloisField}\ q\ 2)^\times \to$ `GL2 q` obtained by applying `Units.map` to the multiplicative map that sends $\alpha$ to the matrix of the left-multiplication operator $\mathrm{Algebra.lmul}$ by $\alpha$, computed in the $\mathbb{Z}/q$-basis `quadBasis q` of $\mathrm{GaloisField}\ q\ 2$ indexed by $\mathrm{Fin}\ 2$ (this basis comes from the equality $\dim_{\mathbb{Z}/q}\mathrm{GaloisField}\ q\ 2 = 2$). The assertion is that the image of $c$ under the map of unit groups induced by the structure morphism $\mathbb{Z}/q \to \mathrm{GaloisField}\ q\ 2$, pushed through `torus q`, equals `scalarElem q c`.
--
--   This records that the (non-split) torus embedding of $\mathbb{F}_{q^2}^\times$ into $GL_2(\mathbb{F}_q)$ restricts on the prime field $\mathbb{F}_q^\times$ to the centre, consisting of scalar matrices. It is used in the analysis of cuspidal types, namely in [`CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq`](thm.html#CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq) and [`CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv`](thm.html#CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv), where a representation with prescribed central behaviour must be controlled on the torus, so that only characters of $\mathbb{F}_{q^2}^\times$ trivial on $\mathbb{F}_q^\times$ can occur.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_torus_unitsMap_algebraMap.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.torus_unitsMap_algebraMap (q : ℕ) [Fact q.Prime] (c : (ZMod q)ˣ) :
    torus q (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = scalarElem q c := by sorry
