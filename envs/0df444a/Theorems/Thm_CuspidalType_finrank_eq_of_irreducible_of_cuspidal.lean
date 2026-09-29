-- Prove2me | Theorems.Thm_CuspidalType_finrank_eq_of_irreducible_of_cuspidal
-- name    : CuspidalType.finrank_eq_of_irreducible_of_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/3c9433a6-a149-57ab-bf24-bd3ec07d0d53
-- title:
--   Cuspidal irreducible representations of GL₂(𝔽_q) have dimension q-1
-- statement:
--   Let $q$ be a prime natural number and let $K$ be an algebraically closed field of characteristic zero. Let $V$ be a non-zero finite-dimensional $K$-vector space, and let $\rho$ be a representation of the group $\mathrm{GL}_2(\mathbb{Z}/q) =$ `GL2 q` of invertible $2\times 2$ matrices over $\mathbb{Z}/q$ on $V$. Two hypotheses are imposed. First, $\rho$ is irreducible in the sense that every subrepresentation of $\rho$ whose underlying submodule is not the zero submodule has underlying submodule all of $V$. Second, $\rho$ is cuspidal in the sense that the only vector $v \in V$ satisfying $\rho(\mathrm{unipotent}\,q\,t)v = v$ for every $t \in \mathbb{Z}/q$ is $v = 0$; here `unipotent q t` denotes the element of $\mathrm{GL}_2(\mathbb{Z}/q)$ given by the upper triangular matrix $\begin{pmatrix}1 & t\\ 0 & 1\end{pmatrix}$ together with its inverse $\begin{pmatrix}1 & -t\\ 0 & 1\end{pmatrix}$. The conclusion is that the $K$-dimension of $V$ equals $q - 1$ (natural number subtraction).
--
--   This is the dimension formula for the cuspidal, or discrete series, representations of $\mathrm{GL}_2$ of a prime field, with irreducibility expressed through subrepresentations and cuspidality through the absence of vectors fixed by the upper unipotent subgroup. It is used in the analysis of characters of such representations, in particular for the value at a unipotent element and for the construction of a representation of a given cuspidal type from an irreducible cuspidal representation with prescribed central character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_finrank_eq_of_irreducible_of_cuspidal.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.finrank_eq_of_irreducible_of_cuspidal
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) :
    Module.finrank K V = q - 1 := by sorry
