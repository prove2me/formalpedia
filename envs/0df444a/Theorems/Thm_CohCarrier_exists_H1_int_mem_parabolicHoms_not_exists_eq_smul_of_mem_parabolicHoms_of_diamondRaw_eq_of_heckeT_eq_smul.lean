-- Prove2me | Theorems.Thm_CohCarrier_exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul
-- name    : CohCarrier.exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/90e5d8c8-3197-50ac-bf98-5bd6ad5ed4bc
-- title:
--   Integral p-primitive parabolic class lifting a mod p eigenvector
-- statement:
--   Let $p$ be a prime, let $N$ be a nonzero natural number with $4 \le N$, and let $\kappa$ be a field of characteristic $p$. Write $\Gamma =$ [`CohCarrier.GammaH N ⊥`](def/CohCarrier_Level.html#L133), the subgroup of $SL(2,\mathbb{Z})$ consisting of the matrices of $\Gamma_0(N)$ whose image under `gamma0Units N` lies in the trivial subgroup of $(\mathbb{Z}/N)^\times$, and for an abelian group $A$ write $H^1 =$ [`CohCarrier.H1 N ⊥ A`](def/CohCarrier_Level.html#L162) for the group of additive homomorphisms $\mathrm{Additive}\,\Gamma \to A$. Suppose given $v \in H^1$ with coefficients in $\kappa$ such that: $v \ne 0$; $v$ is parabolic, i.e. $v(\gamma) = 0$ for every $\gamma \in \Gamma$ with $\operatorname{tr}(\gamma)^2 = 4$; $v$ is fixed by every operator [`CohCarrier.diamondRaw N ⊥ κ σ`](def/CohCarrier_Level.html#L291) (precomposition with conjugation by $\sigma$) for $\sigma \in \Gamma_0(N)$; and, for a set $E \subseteq \mathbb{N}$ and a function $n : \mathbb{N} \to \mathbb{Z}$, one has [`CohCarrier.heckeT N ⊥ ℓ κ`](def/CohCarrier_Level.html#L250) $v = (n_\ell \bmod p)\, v$ for every prime $\ell \notin E$. Then there exists a parabolic $\varphi_0 \in H^1$ with coefficients in $\mathbb{Z}$ such that $\varphi_0$ is not of the form $p\psi$ with $\psi \in H^1$, and such that, for all $\sigma \in \Gamma_0(N)$ and all primes $\ell \notin E$, both `diamondRaw N ⊥ ℤ σ` $\varphi_0 - \varphi_0$ and `heckeT N ⊥ ℓ ℤ` $\varphi_0 - n_\ell \varphi_0$ lie in $p\,H^1$. The divisibility assertions are in the full group of $\mathbb{Z}$-valued homomorphisms, not inside the parabolic submodule.
--
--   This is the descent step from a mod $p$ parabolic Hecke eigenvector for $\Gamma_1(N)$ to an integral parabolic class that is primitive at $p$ and satisfies the same diamond- and Hecke-eigenvalue congruences modulo $p$; it rests on the freeness of integral parabolic cohomology for $N \ge 4$ and on the base-change comparison [`CohCarrier.exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le`](thm.html#CohCarrier.exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le). It is used by [`WeierstrassCurve.exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_apOfModel_level_div_of_forall_linearMap_psCarrier_eq_zero`](thm.html#WeierstrassCurve.exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_apOfModel_level_div_of_forall_linearMap_psCarrier_eq_zero) and [`WeierstrassCurve.exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one`](thm.html#WeierstrassCurve.exists_H1_parabolic_not_dvd_heckeT_congr_apOfModel_of_isEigensystemH1_one), where the eigenvalues $n_\ell$ come from the traces of Frobenius of an elliptic curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (κ : Type) [Field κ] [CharP κ p]
    (v : CohCarrier.H1 N ⊥ κ) (hv : v ≠ 0)
    (hpar : v ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ)
    (hdia : ∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ v = v)
    (E : Set ℕ) (n : ℕ → ℤ)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ E →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N ⊥ ℓ κ v = (n ℓ : κ) • v) :
    ∃ φ₀ : CohCarrier.H1 N ⊥ ℤ,
      φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊥) ℤ ∧
      (¬ ∃ ψ : CohCarrier.H1 N ⊥ ℤ, φ₀ = (p : ℤ) • ψ) ∧
      (∀ σ : CongruenceSubgroup.Gamma0 N, ∃ ψ : CohCarrier.H1 N ⊥ ℤ,
        CohCarrier.diamondRaw N ⊥ ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ E →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ ψ : CohCarrier.H1 N ⊥ ℤ, CohCarrier.heckeT N ⊥ ℓ ℤ φ₀ - (n ℓ) • φ₀ = (p : ℤ) • ψ) := by sorry
