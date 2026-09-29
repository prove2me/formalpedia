-- Prove2me | Theorems.Thm_AutomorphicForm_IsRegularSemisimple_mul_comm_of_mem_centralizer
-- name    : AutomorphicForm.IsRegularSemisimple.mul_comm_of_mem_centralizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/68a7c2f5-346b-52e9-bd76-3d67402d1178
-- title:
--   Centralisers of regular semisimple elements in GL₂ commute
-- statement:
--   Let $A$ be a commutative ring and let $g \in GL_2(A)$ be regular semisimple in the sense of the project's predicate [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402), i.e. the discriminant $\operatorname{tr}(g)^2 - 4\det(g)$ of the underlying $2\times 2$ matrix is a unit of $A$. Let $s$ and $t$ be elements of $GL_2(A)$ lying in the centraliser of the singleton $\{g\}$ as a subgroup of $GL_2(A)$, i.e. each of $s$ and $t$ commutes with $g$ in the group $GL_2(A)$. The conclusion is that $s$ and $t$ commute with one another: $st = ts$. Nothing is assumed about the characteristic of $A$, and no invertibility beyond that of the discriminant and of $g$, $s$, $t$ themselves is used; the statement is the commutativity assertion for the centraliser of a single regular semisimple element, not a description of that centraliser as a torus.
--
--   This is the elementary fact that the commutant of a regular semisimple $2\times2$ matrix is commutative, in the form needed over an arbitrary commutative base ring. It is used in the construction of Haar measures and covolumes on centralisers and twisted centralisers, specifically by [`AutomorphicForm.exists_haar_sigmaCentralizer_centralizer_covolume_and_twistedOrbital_eq_of_normClassMap_eq_of_areMatchingOn`](thm.html#AutomorphicForm.exists_haar_sigmaCentralizer_centralizer_covolume_and_twistedOrbital_eq_of_normClassMap_eq_of_areMatchingOn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsRegularSemisimple_mul_comm_of_mem_centralizer.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.IsRegularSemisimple.mul_comm_of_mem_centralizer
    (A : Type) [CommRing A] (g : GL (Fin 2) A) (hg : AutomorphicForm.IsRegularSemisimple g)
    (s t : GL (Fin 2) A) (hs : s ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) :
    s * t = t * s := by sorry
