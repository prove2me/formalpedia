-- Prove2me | Theorems.Thm_CuspidalType_exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm
-- name    : CuspidalType.exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/0eea3dbb-acec-58d3-a551-bc1a25f64c86
-- title:
--   Equivariant projector onto the cuspidal part of ρ
-- statement:
--   Let $q$ be a prime and let $\mathrm{GL}_2(q)$ denote the general linear group of $2\times 2$ matrices over $\mathbb{Z}/q$, writing $u_t$ for the element with matrix $\begin{pmatrix}1&t\\0&1\end{pmatrix}$ and inverse $\begin{pmatrix}1&-t\\0&1\end{pmatrix}$, for $t \in \mathbb{Z}/q$. Let $K$ be a field of characteristic zero, let $V$ be a $K$-vector space (no finiteness hypothesis), and let $\rho$ be a representation of $\mathrm{GL}_2(q)$ on $V$ over $K$. Let $\Gamma$ be a set of $K$-linear endomorphisms of $V$ such that every $T \in \Gamma$ satisfies $T \circ \rho(g) = \rho(g) \circ T$ for all $g \in \mathrm{GL}_2(q)$. The assertion is that there exists a $K$-linear endomorphism $e_C$ of $V$ with the following four properties: first, if $v \in V$ satisfies $\sum_{t \in \mathbb{Z}/q} \rho(u_t)\rho(g) v = 0$ for every $g \in \mathrm{GL}_2(q)$ (the sums and products being taken in the endomorphism ring of $V$), then $e_C v = v$; second, $e_C \circ \rho(g) = \rho(g) \circ e_C$ for all $g$; third, $e_C \circ T = T \circ e_C$ for every $T \in \Gamma$; and fourth, $\sum_{t \in \mathbb{Z}/q} \rho(u_t)\rho(g)(e_C v) = 0$ for all $v \in V$ and all $g$. Thus $e_C$ restricts to the identity on the subspace annihilated by all the unipotent-averaging operators $\sum_t \rho(u_t)\rho(g)$, maps $V$ into that subspace, and commutes with $\rho$ and with $\Gamma$; idempotence is not stated explicitly, though it follows from the first and fourth properties.
--
--   This is the construction of the canonical projector onto the cuspidal part of a characteristic-zero representation of $\mathrm{GL}_2(\mathbb{F}_q)$, the cuspidal part being cut out by the vanishing of the averages over the standard unipotent subgroup translated by all group elements; semisimplicity of $K[\mathrm{GL}_2(\mathbb{F}_q)]$ makes the projector central, whence the commutation with an arbitrary family $\Gamma$ of equivariant endomorphisms. It supplies the projector $e_C$ used in the cuspidal specialisation of the full-level Tate module, and is cited by the three full-level statements producing such a specialisation map from a semistable covering and model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspidalType.exists_linearMap_apply_eq_self_of_forall_sum_unipotent_eq_zero_and_comm
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [CharZero K]
    (V : Type*) [AddCommGroup V] [Module K V]
    (ρ : Representation K (CuspidalType.GL2 q) V)
    (Γ : Set (V →ₗ[K] V)) (hΓ : ∀ T ∈ Γ, ∀ g : CuspidalType.GL2 q, T ∘ₗ ρ g = ρ g ∘ₗ T) :
    ∃ eC : V →ₗ[K] V,
      (∀ v : V, (∀ g : CuspidalType.GL2 q, (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) * ρ g) v = 0) → eC v = v) ∧
      (∀ g : CuspidalType.GL2 q, eC ∘ₗ ρ g = ρ g ∘ₗ eC) ∧
      (∀ T ∈ Γ, eC ∘ₗ T = T ∘ₗ eC) ∧
      (∀ (v : V) (g : CuspidalType.GL2 q), (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) * ρ g) (eC v) = 0) := by sorry
