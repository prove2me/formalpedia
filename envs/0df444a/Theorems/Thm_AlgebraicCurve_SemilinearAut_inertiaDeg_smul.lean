-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul
-- name    : AlgebraicCurve.SemilinearAut.inertiaDeg_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/251f8687-be65-5238-922c-b868e9175bff
-- title:
--   Invariance of inertia degree under intertwined semilinear automorphisms
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structure maps forming a scalar tower, and with $F'$ integral over $F$. Here a semilinear automorphism in `SemilinearAut K F` is a pair $(\sigma,\tau)$ consisting of a ring automorphism $\sigma$ of $F$ and a ring automorphism $\tau$ of $K$ such that $\sigma(\iota_{K,F}(a)) = \iota_{K,F}(\tau a)$ for all $a \in K$, these pairs forming a subgroup of $\mathrm{Aut}(F) \times \mathrm{Aut}(K)$, and likewise for `SemilinearAut K F'`. Given $g \in$ `SemilinearAut K F` and $g' \in$ `SemilinearAut K F'` satisfying `IntertwinesAlong`, that is $g' \cdot \iota_{F,F'}(x) = \iota_{F,F'}(g \cdot x)$ for every $x \in F$, and given a place $w$ of $F'$ over $K$ (a valuation subring of $F'$, distinct from $F'$, containing the image of $K$, and a principal ideal ring), the conclusion is the equality of inertia degrees $f(g' \cdot w \mid F) = f(w \mid F)$, where $g' \cdot w$ is the pointwise translate of $w$ by $g'$ and where $f(\,\cdot \mid F)$ denotes the dimension, as a vector space over the residue field of the place of $F$ obtained by pulling the given place back along $\iota_{F,F'}$, of the residue field of that place of $F'$.
--
--   This is the invariance of the residue (inertia) degree in a tower $F \subseteq F'$ under a compatible pair of semilinear automorphisms of $F$ and $F'$; it is the residue-degree half of the statement that such a pair acts on places compatibly with the tower. It is used for [`AlgebraicCurve.Place.inertiaDeg_eq_of_restrict_eq`](thm.html#AlgebraicCurve.Place.inertiaDeg_eq_of_restrict_eq) and for [`AlgebraicCurve.SemilinearAut.pushforward_smul`](thm.html#AlgebraicCurve.SemilinearAut.pushforward_smul). The inertia degree is a vector-space dimension, so it takes the value $0$ on infinite residue extensions; the assertion is an equality of the two dimensions and carries no finiteness information.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.SemilinearAut.inertiaDeg_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') : (g' • w).inertiaDeg F = w.inertiaDeg F := by sorry
