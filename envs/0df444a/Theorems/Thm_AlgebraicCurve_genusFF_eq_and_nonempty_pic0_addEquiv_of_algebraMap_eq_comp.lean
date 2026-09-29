-- Prove2me | Theorems.Thm_AlgebraicCurve_genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp
-- name    : AlgebraicCurve.genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/9c4313b4-e10a-566a-ba23-84ec035da077
-- title:
--   Genus and Pic⁰ under renaming the constant field
-- statement:
--   Let $k$, $K$ and $F$ be fields, with $F$ an algebra over $K$ and also an algebra over $k$, let $e : k \simeq K$ be an isomorphism of rings, and assume the compatibility $\mathrm{algebraMap}\,k\,F = (\mathrm{algebraMap}\,K\,F)\circ e$, i.e. the structure map $k \to F$ factors as $e$ followed by the structure map $K \to F$. The conclusion is twofold. First, the two genera agree: $\mathtt{genusFF}\,k\,F = \mathtt{genusFF}\,K\,F$, where $\mathtt{genusFF}$ of a pair (constant field, ambient field) is the rank, over the named constant field, of the first repartition cohomology module $\mathtt{H1}$ of the zero divisor. Second, the group of degree-zero divisor classes of $F$ over $k$ is isomorphic to that of $F$ over $K$: the type $\mathtt{Pic0}$ is formed from the finitely supported $\mathbb{Z}$-valued functions on the places of $F$ over the given constant field, by taking the kernel of the degree map and quotienting by the subgroup of divisors of the shape $v \mapsto \mathrm{ord}_v(f)$ for some $f \neq 0$ in $F$, and the assertion is that the type of additive group isomorphisms $\mathtt{Pic0}\,k\,F \simeq \mathtt{Pic0}\,K\,F$ is nonempty (an isomorphism exists, without a specified choice).
--
--   This is a transport-of-structure device: the places, divisors, degrees, principal divisors and repartition cohomology of a function field depend only on the image of the constant field in $F$, so presenting the constants under a different but isomorphic name changes neither the genus nor the degree-zero divisor class group. It is used to convert results proved for a function field whose constants arise as a residue field into results over an abstractly given constant field, and is cited in the bounds on the torsion of $\mathtt{Pic0}$ in terms of the genus and in the constructions of good constant reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp
    (k K F : Type*) [Field k] [Field K] [Field F] [Algebra K F] [Algebra k F]
    (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    genusFF k F = genusFF K F ∧ Nonempty (Pic0 k F ≃+ Pic0 K F) := by sorry
