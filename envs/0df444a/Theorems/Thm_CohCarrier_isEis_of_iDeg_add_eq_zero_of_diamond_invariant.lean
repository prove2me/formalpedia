-- Prove2me | Theorems.Thm_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant
-- name    : CohCarrier.isEis_of_iDeg_add_eq_zero_of_diamond_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/da02a063-75d3-555a-a127-0006cbfcba4c
-- title:
--   Ihara's lemma at Γ_H from Γ₀ at unit index
-- statement:
--   Fix a commutative ring $R$, an $R$-module $A$, a nonzero natural number $\ell_0$, nonzero natural numbers $N$ and $q$, and subgroups $H \le (\mathbb{Z}/N)^\times$, $H' \le (\mathbb{Z}/Nq)^\times$. Here $\mathtt{H1}\,M\,K\,A$ denotes the additive homomorphisms from the additivisation of $\Gamma_K(M) =$ `GammaH M K` to $A$, and for data $h$ of type `LevelLE M M' K K' d` (asserting $M \mid M'$, $d \mid M'/M$, and that reduction modulo $M$ carries $K'$ into $K$) the map `iDeg'` is precomposition with the homomorphism `iotaDeg` $\colon \Gamma_{K'}(M') \to \Gamma_K(M)$ given by the lowering conjugation of level $d$. Assume given `LevelLE` data for $(H,H')$ with $d = 1$ and with $d = q$, and likewise for the pair of full unit groups with $d = 1$ and $d = q$; assume $\ell_0$ is prime and $\ell_0 \nmid Nq$; assume the images in $R$ of the indices $[(\mathbb{Z}/N)^\times : H]$ and $[(\mathbb{Z}/Nq)^\times : H']$ are units; and assume, at the full level structure, that every pair $g_0, h_0 \in \mathtt{H1}\,N\,\top\,A$ with $\iota_1^* g_0 + \iota_q^* h_0 = 0$ satisfies $T_{\ell_0} g_0 = (\ell_0 + 1) g_0$ and $T_{\ell_0} h_0 = (\ell_0+1) h_0$, where $T_{\ell_0}$ is `heckeT`. Then for $g, h \in \mathtt{H1}\,N\,H\,A$ invariant under `diamondRaw` for every $\sigma \in \Gamma_0(N)$ (precomposition with conjugation by $\sigma$) and satisfying $\iota_1^* g + \iota_q^* h = 0$, one has $T_{\ell_0} g = ((\ell_0 : R) + 1) \cdot g$ and $T_{\ell_0} h = ((\ell_0:R)+1)\cdot h$.
--
--   This is the transfer of Ihara's lemma, in the kernel-pair (Eisenstein) formulation, from the level structure $\Gamma_0(N)$ to $\Gamma_H(N)$, for classes invariant under the diamond action and under the hypothesis that the relevant indices are invertible in the coefficient ring; the statement at $\top$ is taken as a hypothesis rather than proved here. It feeds the construction of corner refinements at level $Nq$ and the level-lowering step for local Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant.lean

import Mathlib
import Definitions.Def_CohCarrier_Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.isEis_of_iDeg_add_eq_zero_of_diamond_invariant
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ) (H' : Subgroup (ZMod (N * q))ˣ)
    (h₁ : LevelLE N (N * q) H H' 1) (hq : LevelLE N (N * q) H H' q)
    (h₁top : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hqtop : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    (hℓ : ℓ₀.Prime) (hℓNq : ¬ ℓ₀ ∣ N * q)
    (hunit : IsUnit ((H.index : ℕ) : R)) (hunit' : IsUnit ((H'.index : ℕ) : R))
    (hihara_top : ∀ g₀ h₀ : H1 N ⊤ A,
      iDeg' N (N * q) ⊤ ⊤ 1 A h₁top g₀ + iDeg' N (N * q) ⊤ ⊤ q A hqtop h₀ = 0 →
        IsEis R A N ⊤ ℓ₀ g₀ ∧ IsEis R A N ⊤ ℓ₀ h₀)
    (g h : H1 N H A)
    (hg : ∀ σ : Gamma0 N, diamondRaw N H A σ g = g) (hh : ∀ σ : Gamma0 N, diamondRaw N H A σ h = h)
    (hgh : iDeg' N (N * q) H H' 1 A h₁ g + iDeg' N (N * q) H H' q A hq h = 0) :
    IsEis R A N H ℓ₀ g ∧ IsEis R A N H ℓ₀ h := by sorry
