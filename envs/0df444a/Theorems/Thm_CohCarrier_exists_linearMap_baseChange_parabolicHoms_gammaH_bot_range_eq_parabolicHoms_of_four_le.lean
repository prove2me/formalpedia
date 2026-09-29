-- Prove2me | Theorems.Thm_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le
-- name    : CohCarrier.exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/336224a2-6bd1-510b-b7ed-3d8e55bc132f
-- title:
--   Base change of parabolic cohomology of Γ₁(N), N≥ 4
-- statement:
--   Fix a prime $p$, an integer $N \neq 0$ with $4 \le N$, and a field $\kappa$ of characteristic $p$. Write $\Gamma =$ [`CohCarrier.GammaH N ⊥`](def/CohCarrier_Level.html#L133), the subgroup of $SL(2,\mathbb{Z})$ consisting of the matrices of $\Gamma_0(N)$ whose associated unit $d \bmod N$ lies in the trivial subgroup of $(\mathbb{Z}/N)^\times$, i.e. $\Gamma_1(N)$. For a commutative ring $R$ and an $R$-module $A$, [`ModularCurve.Period.parabolicHoms R Γ A`](def/ModularCurve_PeriodMap.html#L62) denotes the $R$-submodule of additive homomorphisms $\varphi : \mathrm{Additive}\,\Gamma \to A$ vanishing on every $\gamma$ with $\mathrm{tr}(\gamma)^2 = 4$. The assertion is that there exists a $\kappa$-linear map $\iota$ from $\kappa \otimes_{\mathbb{Z}} \mathrm{parabolicHoms}_{\mathbb{Z}}(\Gamma,\mathbb{Z})$ to the group $\mathrm{Additive}\,\Gamma \to_+ \kappa$ of all additive characters of $\Gamma$ with values in $\kappa$, such that: (i) for all $r \in \kappa$, all parabolic integral characters $x$ and all $\gamma \in \Gamma$, $\iota(r \otimes x)(\gamma) = r \cdot \overline{x(\gamma)}$, where $\overline{\,\cdot\,}$ is the image of an integer in $\kappa$; (ii) $\iota$ is injective; and (iii) the range of $\iota$ is exactly $\mathrm{parabolicHoms}_{\kappa}(\Gamma,\kappa)$.
--
--   This is the statement that parabolic cohomology of $\Gamma_1(N)$ with $N \ge 4$ commutes with base change from $\mathbb{Z}$ to a field of arbitrary characteristic, the point being that $\Gamma_1(N)$ has no non-trivial elements of finite order in that range, so no torsion phenomena intervene. It is used in the construction of an integral parabolic class with prescribed diamond and Hecke behaviour that is not a scalar multiple of another such class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups TensorProduct

theorem CohCarrier.exists_linearMap_baseChange_parabolicHoms_gammaH_bot_range_eq_parabolicHoms_of_four_le
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (κ : Type) [Field κ] [CharP κ p] :
    ∃ ι : κ ⊗[ℤ] ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) ℤ) →ₗ[κ]
        CohCarrier.H1 N ⊥ κ,
      (∀ (r : κ) (x : ↥(ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) ℤ))
          (γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))),
          ι (r ⊗ₜ[ℤ] x) (Additive.ofMul γ) =
            r * ((x : Additive ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) →+ ℤ) (Additive.ofMul γ) : κ)) ∧
      Function.Injective ι ∧
      LinearMap.range ι = ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) κ := by sorry
