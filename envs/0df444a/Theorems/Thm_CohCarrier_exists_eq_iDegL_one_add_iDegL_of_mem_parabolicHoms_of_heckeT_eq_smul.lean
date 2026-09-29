-- Prove2me | Theorems.Thm_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul
-- name    : CohCarrier.exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/7047bd5b-0578-5007-9e6d-bf541b5aaebd
-- title:
--   Parabolic eigenclasses at level Mp occurring at level M are old
-- statement:
--   Let $F$ be a field of characteristic zero, let $M$ and $p$ be nonzero natural numbers with $p$ prime, $Mp \neq 0$ and $p \nmid M$, and fix data `h1` and `hp` witnessing `LevelLE M (M*p) ⊤ ⊤ 1` and `LevelLE M (M*p) ⊤ ⊤ p`, that is, $M \mid Mp$ together with $1 \mid (Mp)/M$, resp. $p \mid (Mp)/M$, and the (vacuous for the full unit group) condition on reduction of units. Let $S$ be a finite set of naturals and $a : \mathbb{N} \to F$. Here $H^1(L,\top;F)$ means the $F$-module of homomorphisms from $\Gamma_H(L)=\Gamma_0(L)$, written additively, to $F$, `parabolicHoms` is the submodule of those vanishing on every element whose trace has square $4$, `heckeT` is the transfer-defined Hecke operator, and `iDegL M (M*p) ⊤ ⊤ d F F` is precomposition with the conjugation $\gamma \mapsto \delta_d \gamma \delta_d^{-1}$ of `iotaDeg`, mapping $H^1(M)$ into $H^1(Mp)$. Assume $w \in H^1(Mp,\top;F)$ is parabolic and satisfies $T_\ell w = a_\ell w$ for every prime $\ell \notin S$ with $\ell \nmid Mp$, and that some nonzero parabolic $w_0 \in H^1(M,\top;F)$ satisfies the same eigenvalue equations at level $M$ for those $\ell$. Then there exist parabolic $y_1, y_2 \in H^1(M,\top;F)$, each satisfying $T_\ell y_i = a_\ell y_i$ for all such $\ell$, with $w = \mathrm{iDegL}_1(y_1) + \mathrm{iDegL}_p(y_2)$.
--
--   This is the cohomological form of the theory of oldforms at a prime $p$ not dividing the level: a parabolic Hecke eigenclass on $\Gamma_0(Mp)$ whose eigenvalue system away from $S$ already occurs at level $M$ lies in the span of the two degeneracy pull-backs from level $M$. It is used in the bound on the rank of the corner eigenspace attached to a unit root in [`CuspForm.heckeLocal.finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul`](thm.html#CuspForm.heckeLocal.finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul); the passage from $\mathbb{C}$ to an arbitrary field of characteristic zero uses the Eichler–Shimura description of the parabolic cohomology and an integral basis of it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier

theorem CohCarrier.exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul
    {F : Type} [Field F] [CharZero F]
    (M p : ℕ) [NeZero M] [Fact p.Prime] [NeZero (M * p)] (hpM : ¬ p ∣ M)
    (h1 : LevelLE M (M * p) ⊤ ⊤ 1) (hp : LevelLE M (M * p) ⊤ ⊤ p)
    (S : Finset ℕ) (a : ℕ → F)
    (w : H1 (M * p) ⊤ F) (hw : w ∈ ModularCurve.Period.parabolicHoms F (GammaH (M * p) ⊤) F)
    (heig : ∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
      heckeT (M * p) ⊤ ℓ F w = a ℓ • w)
    (hocc : ∃ w₀ : H1 M ⊤ F, w₀ ≠ 0 ∧ w₀ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p), heckeT M ⊤ ℓ F w₀ = a ℓ • w₀) :
    ∃ y₁ y₂ : H1 M ⊤ F,
      y₁ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F ∧
      y₂ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
        heckeT M ⊤ ℓ F y₁ = a ℓ • y₁ ∧ heckeT M ⊤ ℓ F y₂ = a ℓ • y₂) ∧
      w = iDegL M (M * p) ⊤ ⊤ 1 F F h1 y₁ + iDegL M (M * p) ⊤ ⊤ p F F hp y₂ := by sorry
