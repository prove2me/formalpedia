-- Prove2me | Theorems.Thm_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index
-- name    : CohCarrier.injective_iDeg_one_and_range_eq_of_isUnit_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6fe78f25-370b-5de1-a956-7e3038b4a965
-- title:
--   Degree-one restriction and transfer between Γ_H(M) and Γ₀(M)
-- statement:
--   Fix a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, a commutative ring $R$ and an $R$-module $A$ (an additive abelian group with an $R$-module structure). Let $h$ witness [`CohCarrier.LevelLE M M ⊤ H 1`](def/CohCarrier_Level.html#L330), i.e. $M \mid M$, $1 \mid M/M$, and every unit in $H$ maps into $\top$ under reduction — conditions that hold trivially, $h$ being carried as data. Assume moreover that the image of the index $[(\mathbb{Z}/M)^\times : H]$ in $R$ is a unit. Here $\Gamma_H(M) \le SL(2,\mathbb{Z})$ is the set of matrices of $\Gamma_0(M)$ whose associated unit lies in $H$, so $\Gamma_\top(M) = \Gamma_0(M)$; `H1 M H A` is the group of homomorphisms $\Gamma_H(M) \to A$; for $d = 1$ the degeneracy map `iotaDeg` is the inclusion $\Gamma_H(M) \hookrightarrow \Gamma_0(M)$, `iDeg'` is restriction of homomorphisms along it, `jDeg` is the transfer (corestriction) in the opposite direction, and `diamondRaw M H A σ` is precomposition with $\gamma \mapsto \sigma\gamma\sigma^{-1}$ for $\sigma \in \Gamma_0(M)$. The conclusion asserts four things: the image of $\Gamma_H(M)$ in $\Gamma_0(M)$ has index $[(\mathbb{Z}/M)^\times : H]$; restriction `iDeg'` is injective; its range is exactly the set of $\varphi$ fixed by $\mathrm{diamondRaw}\,\sigma$ for all $\sigma \in \Gamma_0(M)$; and for every such diamond-invariant $\varphi$ one has $\mathrm{iDeg'}(\mathrm{jDeg}\,\varphi) = [(\mathbb{Z}/M)^\times : H] \cdot \varphi$.
--
--   This is the degree-one, $\mathrm{Hom}$-coefficient case of restriction–corestriction for the normal subgroup $\Gamma_H(M) \trianglelefteq \Gamma_0(M)$: once the index $[(\mathbb{Z}/M)^\times : H]$ is invertible in the coefficients, restriction identifies the $\Gamma_0(M)$-level characters with the diamond-invariant $\Gamma_H(M)$-level characters, with the transfer providing the inverse up to the index. It is used downstream in the comparison of corner submodules at the two levels and in the construction of self-adjoint pairings compatible with degeneracy maps, the step that allows an auxiliary prime whose diamond group has order prime to the residue characteristic to be removed from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem CohCarrier.injective_iDeg_one_and_range_eq_of_isUnit_index
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (h : CohCarrier.LevelLE M M ⊤ H 1)
    (hunit : IsUnit ((H.index : ℕ) : R)) :
    (CohCarrier.iotaDeg M M ⊤ H 1 h).range.index = H.index ∧
    Function.Injective (CohCarrier.iDeg' M M ⊤ H 1 A h) ∧
    Set.range (CohCarrier.iDeg' M M ⊤ H 1 A h) =
      {φ | ∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ} ∧
    ∀ φ : CohCarrier.H1 M H A, (∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) →
      CohCarrier.iDeg' M M ⊤ H 1 A h (CohCarrier.jDeg M M ⊤ H 1 A h φ) = H.index • φ := by sorry
