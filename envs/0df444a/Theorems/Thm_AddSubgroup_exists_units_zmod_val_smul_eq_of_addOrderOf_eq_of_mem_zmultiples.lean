-- Prove2me | Theorems.Thm_AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples
-- name    : AddSubgroup.exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/21b78e19-64b5-5549-87c9-3b5ff607af4a
-- title:
--   Equal-order points in one cyclic subgroup differ by a unit of ℤ/ℓ
-- statement:
--   Let $G$ be an additive commutative group, let $\ell$ be a natural number that is nonzero, and let $P, P' \in G$. Assume that the additive order of $P$ equals $\ell$, that the additive order of $P'$ equals $\ell$, and that $P'$ lies in `AddSubgroup.zmultiples P`, i.e. $P' = k \cdot P$ for some integer $k$. Then there exists a unit $d$ of the ring $\mathbb{Z}/\ell$ such that $P' = \tilde{d} \cdot P$, where $\tilde{d}$ is the canonical natural-number representative of $d$ in $\{0, \dots, \ell-1\}$ (the value `ZMod.val` of the underlying element of $\mathbb{Z}/\ell$) and the action is the $\mathbb{N}$-scalar multiplication on $G$. Thus two elements of exact order $\ell$ generating the same cyclic subgroup are related by multiplication by an invertible residue class modulo $\ell$, with the multiplier produced as an honest unit of $\mathbb{Z}/\ell$ rather than merely as an integer coprime to $\ell$.
--
--   This is the elementary statement that the generators of a cyclic group of order $\ell$ form a single orbit under $(\mathbb{Z}/\ell)^\times$. It is used in the treatment of diamond operators on full-level modular curves, where it supplies the transitivity on points of exact order $\ell$ inside a fixed cyclic subgroup of that order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddSubgroup.exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples
    {G : Type*} [AddCommGroup G] (ℓ : ℕ) [NeZero ℓ] (P P' : G)
    (hP : addOrderOf P = ℓ) (hP' : addOrderOf P' = ℓ) (h : P' ∈ AddSubgroup.zmultiples P) :
    ∃ d : (ZMod ℓ)ˣ, P' = (d : ZMod ℓ).val • P := by sorry
