-- Prove2me | Theorems.Thm_CuspidalType_charpoly_scalarElem_mul_unipotent_eq_cyclotomic_of_cuspidal
-- name    : CuspidalType.charpoly_scalarElem_mul_unipotent_eq_cyclotomic_of_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/5fbf2745-3117-5927-8e78-90597e3c1265
-- title:
--   Cuspidal representations: unipotent charpoly is Φ_q
-- statement:
--   Let $q$ be a prime, let $K$ be a field, and let $V$ be a finite-dimensional $K$-vector space. Let $\rho$ be a representation of $\mathrm{GL}_2(\mathbb{Z}/q) =$ `Matrix.GeneralLinearGroup (Fin 2) (ZMod q)` on $V$ over $K$. Assume three conditions: the $K$-dimension of $V$ equals $q-1$ (truncated subtraction of naturals); cuspidality in the form that a vector $v \in V$ fixed by $\rho(u_t)$ for every $t \in \mathbb{Z}/q$, where $u_t$ is the unipotent unit with matrix $\begin{pmatrix}1&t\\0&1\end{pmatrix}$ and inverse $\begin{pmatrix}1&-t\\0&1\end{pmatrix}$, must be zero; and triviality of the central character, in the form that $\rho$ sends the scalar matrix $c \cdot I_2$, for every unit $c$ of $\mathbb{Z}/q$, to the identity linear map. Then for every unit $z$ of $\mathbb{Z}/q$ and every nonzero $t \in \mathbb{Z}/q$, the characteristic polynomial of the endomorphism $\rho(z \cdot I_2 \cdot u_t)$ of $V$ equals the $q$-th cyclotomic polynomial over $K$, that is $1 + X + \dots + X^{q-1}$ since $q$ is prime.
--
--   This records the conjugacy-class data of a cuspidal type on the non-trivial unipotent classes and their central translates: the three hypotheses are exactly the dimension, cuspidality and trivial-central-character conditions, so no character of $\mathbb{F}_{q^2}^\times$ enters. It is used in [`CuspidalType.IsCuspidalOfType.exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map`](thm.html#CuspidalType.IsCuspidalOfType.exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map), which compares the characteristic polynomials of a cuspidal type and of an induced representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_charpoly_scalarElem_mul_unipotent_eq_cyclotomic_of_cuspidal.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.charpoly_scalarElem_mul_unipotent_eq_cyclotomic_of_cuspidal
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (GL2 q) V)
    (hfin : Module.finrank K V = q - 1)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id)
    (z : (ZMod q)ˣ) (t : ZMod q) (ht : t ≠ 0) :
    LinearMap.charpoly (ρ (scalarElem q z * unipotent q t)) = Polynomial.cyclotomic q K := by sorry
