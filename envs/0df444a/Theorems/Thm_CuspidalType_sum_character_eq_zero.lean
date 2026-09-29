-- Prove2me | Theorems.Thm_CuspidalType_sum_character_eq_zero
-- name    : CuspidalType.sum_character_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/98780f06-0541-5c29-9af1-41aa4a65c141
-- title:
--   Character of a cuspidal representation sums to zero
-- statement:
--   Let $q$ be a natural number carrying a `Fact` instance that it is prime, let $K$ be a field and let $V$ be an additive commutative group equipped with a $K$-module structure (no finiteness or finite-dimensionality assumption is made). Let $\rho$ be a $K$-linear representation of the group $\mathrm{GL}_2(\mathbb{Z}/q) =$ `Matrix.GeneralLinearGroup (Fin 2) (ZMod q)` on $V$. Assume the cuspidality hypothesis: every vector $v \in V$ such that $\rho(u(t))v = v$ for all $t \in \mathbb{Z}/q$ is zero, where $u(t)$ denotes the unit of the matrix ring given by $\begin{pmatrix}1&t\\0&1\end{pmatrix}$ with inverse $\begin{pmatrix}1&-t\\0&1\end{pmatrix}$, i.e. no non-zero vector of $V$ is fixed by the whole upper unipotent subgroup. The conclusion is that the sum of the character of $\rho$ over the finite group $\mathrm{GL}_2(\mathbb{Z}/q)$ vanishes: $\sum_{g \in \mathrm{GL}_2(\mathbb{Z}/q)} \operatorname{tr}\rho(g) = 0$ in $K$.
--
--   This is the standard vanishing of the sum of the character of a representation with no upper-unipotent-invariant vectors, equivalently (in characteristic zero) the absence of a trivial constituent in such a representation. It is used in the analysis of cuspidal representations of $\mathrm{GL}_2(\mathbb{F}_q)$, being cited by [`CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central`](thm.html#CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_sum_character_eq_zero.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.sum_character_eq_zero
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) :
    ∑ g : GL2 q, ρ.character g = 0 := by sorry
