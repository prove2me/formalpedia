-- Prove2me | Theorems.Thm_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup
-- name    : AutomorphicForm.existsUnique_bruhatRepresentative_mul_mem_borelSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/730337b9-f16b-526f-bf29-7b74f1b28d32
-- title:
--   Bruhat representatives for Bbackslash GL₂(K)
-- statement:
--   Let $K$ be a field and let $\gamma \in GL_2(K)$. Write $w = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ for `gl2Weyl` and $n(\xi) = \begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ for `unipotentGL2 ξ`, and let `borelSubgroup K` be the subgroup of $GL_2(K)$ consisting of those invertible matrices whose lower-left entry, the $(1,0)$ entry, vanishes (that is, the invertible upper triangular matrices). Attach to each element $o$ of `Option K` the group element $c_o \in GL_2(K)$ defined by $c_{\text{none}} = 1$ and $c_{\text{some }\xi} = w\,n(\xi)$. The assertion is that there is exactly one $o \in$ `Option K` for which $c_o\,\gamma$ lies in `borelSubgroup K`: existence of such an $o$, and equality of any two such. Equivalently, $GL_2(K)$ is the disjoint union of the left cosets $c_o^{-1}\,B$ as $o$ ranges over $\{\ast\} \sqcup K$, so that $\{1\} \cup \{w\,n(\xi) : \xi \in K\}$ is a system of representatives for $B \backslash GL_2(K)$.
--
--   This is the Bruhat decomposition $GL_2 = B \sqcup BwB$ over a field, in the form $BwB = \bigsqcup_{\xi} B\,w\,n(\xi)$, packaged as a statement about a system of representatives of the coset space $B \backslash GL_2(K)$. It is the combinatorial input for unfolding an Eisenstein series as a sum over $B(F) \backslash GL_2(F)$, and is used in the Petersson-product and constant-term computations of the automorphic forms development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup.lean

import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_WeylIntertwining

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.existsUnique_bruhatRepresentative_mul_mem_borelSubgroup
    (K : Type*) [Field K] (γ : GL (Fin 2) K) :
    ∃! o : Option K, (o.elim 1 fun ξ => (gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ ∈ borelSubgroup K := by sorry
