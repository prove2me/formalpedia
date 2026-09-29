-- Prove2me | Theorems.Thm_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
-- name    : CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/59d9fe08-1ae5-5669-a7e4-892b7b03a3f5
-- title:
--   Hecke eigen-relations force the nebentypus character
-- statement:
--   Let $M$ be a nonzero natural number, $k$ an integer, and $g$ a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(M)$ of $\mathrm{SL}(2,\mathbb{Z})$, regarded as a subgroup of $\mathrm{GL}(2,\mathbb{R})$; let $\chi$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$. For a function $f$ on the upper half plane write $a_n(f)$ for the $n$-th coefficient [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) of its $q$-expansion of period $1$, i.e. the $n$-th coefficient of `qExpansion 1 f`. Assume that for every prime $p$ with $p \nmid M$ there is a scalar $\lambda \in \mathbb{C}$ such that for all natural numbers $n$,
--   $$a_{np}(g) + \chi(p \bmod M)\, p^{\,k-1}\cdot\bigl(\text{$a_{n/p}(g)$ if $p \mid n$, else $0$}\bigr) = \lambda\, a_n(g),$$
--   where $n/p$ is natural-number division. Then for every $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ lying in $\Gamma_0(M)$, the weight-$k$ slash action satisfies
--   $$g \mid_k \gamma = \chi\bigl(\gamma_{1,1} \bmod M\bigr)\cdot g$$
--   as functions on the upper half plane, $\gamma_{1,1}$ being the lower-right entry of $\gamma$.
--
--   This is the classical statement that a cusp form on $\Gamma_1(M)$ whose $q$-expansion satisfies the $U_p + \chi(p)p^{k-1}V_p$ eigen-relations at all primes $p \nmid M$ transforms under the diamond operators by $\chi$, that is, has nebentypus $\chi$ on $\Gamma_0(M)$. It is used in the Deligne–Serre passage from weight-one Hecke eigenforms to Galois representations, and in the associated constructions of eigenvalue subalgebras and of lattice realisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
    {M : ℕ} [NeZero M] (k : ℤ)
    (g : CuspForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (χ : DirichletCharacter ℂ M)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑g) (n * p)
        + χ (p : ZMod M) * (p : ℂ) ^ (k - 1)
            * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0)
        = lam * ModularFormClass.qCoeff (⇑g) n)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑g : ℍ → ℂ) ∣[k] γ = χ ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ) := by sorry
