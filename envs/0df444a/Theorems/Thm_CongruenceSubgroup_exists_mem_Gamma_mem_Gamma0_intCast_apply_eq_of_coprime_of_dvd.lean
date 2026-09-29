-- Prove2me | Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd
-- name    : CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/7283c1a3-a414-561e-a0e8-6516ad25d7c8
-- title:
--   Diamond lift: prescribed entry in Γ(q)∩Γ₀(M')
-- statement:
--   Let $q$ and $M'$ be natural numbers, both assumed nonzero (as `NeZero` instances), with $q$ and $M'$ coprime, let $\ell$ be a natural number dividing $M'$, and let $d$ be a unit of $\mathbb{Z}/\ell$. The assertion is that there exists $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ (the Mathlib special linear group of $2\times 2$ integral matrices of determinant $1$) lying simultaneously in the principal congruence subgroup $\Gamma(q)$, i.e. the reduction of $\gamma$ modulo $q$ is the identity matrix (equivalently $\gamma_{00}\equiv\gamma_{11}\equiv 1$ and $\gamma_{01}\equiv\gamma_{10}\equiv 0 \pmod q$), and in $\Gamma_0(M')$, i.e. the lower-left entry satisfies $\gamma_{10}\equiv 0 \pmod{M'}$, and such that the image of the lower-right entry $\gamma_{11}\in\mathbb{Z}$ in $\mathbb{Z}/\ell$ equals the image of $d$. Thus every residue class in $(\mathbb{Z}/\ell)^\times$ is realised as the lower-right entry, modulo $\ell$, of a matrix in $\Gamma(q)\cap\Gamma_0(M')$; no condition beyond invertibility modulo $\ell$ is imposed on $d$, and $\ell$ may be $1$ or equal to $M'$.
--
--   This is the standard lifting lemma underlying the definition of the diamond operators $\langle d\rangle$ on modular curves with $\Gamma_1$-type level structure: it produces, for each unit $d$ modulo $\ell$, an element of $\Gamma(q)\cap\Gamma_0(M')$ whose lower-right entry reduces to $d$. It is used in the treatment of diamond operators as level automorphisms of modular curves, in particular in the computations of level-automorphism stabilisers and orbit descriptions at the relevant moduli points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd
    (q M' : ℕ) [NeZero q] [NeZero M'] (hqM' : Nat.Coprime q M') (ℓ : ℕ) (hℓ : ℓ ∣ M') (d : (ZMod ℓ)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ((γ 1 1 : ℤ) : ZMod ℓ) = (d : ZMod ℓ) := by sorry
