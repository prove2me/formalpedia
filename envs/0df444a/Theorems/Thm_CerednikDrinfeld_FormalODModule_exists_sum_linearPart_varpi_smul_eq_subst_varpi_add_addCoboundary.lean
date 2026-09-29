-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary
-- name    : CerednikDrinfeld.FormalODModule.exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/c379e019-6670-59ca-a045-ab87ff13878a
-- title:
--   varpi-equivariance of the cocycle tuple, modulo coboundaries
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $j_0 \colon W(\mathbb{F}_{q^2}) \to k$ a ring homomorphism, where $W(\mathbb{F}_{q^2})$ denotes `Zp2 q`. Let $X_0$ be a special formal $\mathcal{O}_D$-module over $k$ relative to $j_0$ of height $4$: a two-dimensional commutative formal group law $F = X_0.F$ together with series $\mathrm{act}(a)$ and $\varpi$ which are law endomorphisms of $F$ and satisfy the $\mathcal{O}_D$-relations, subject to the predicates `IsSpecial` and `HasHeight 4`. Let $N$ be a formal $\mathcal{O}_D$-module over the dual numbers $k[\varepsilon]$ whose reduction along the first projection $k[\varepsilon] \to k$ is $X_0$, and let $\Gamma_l$, $l \in \{1,2\}$, be power series in two blocks of two variables over $k$, each a symmetric two-cocycle for $F$ (vanishing constant term, invariance under interchanging the two blocks, and the cocycle identity). Assume the group law of $N$ is obtained from that of $F$ by substituting $F_j$ in the first block and $\varepsilon\,\Gamma_j$ in the second, i.e. $N$ is the first-order deformation of $F$ with cocycle tuple $\Gamma$. Then there are series $g_l$ in two variables with zero constant term such that for each $l$, $\sum_i \lambda(\varpi)_{li}\,\Gamma_i = \Gamma_l(\varpi(X),\varpi(Y)) + \partial g_l$, where $\lambda(\varpi)$ is the matrix of degree-one coefficients of $X_0.\varpi$, the pull-back substitutes $\varpi_i$ into each block of variables of $\Gamma_l$, and $\partial g = g(F(X,Y)) - g(X) - g(Y)$.
--
--   This is the $\varpi$-compatibility of the symmetric two-cocycle tuple describing a first-order deformation of a special formal $\mathcal{O}_D$-module: the uniformiser acts on the tuple through its linear part, up to additive coboundaries. It feeds the analysis of deformations over the dual numbers in the Čerednik–Drinfeld setting, and is cited by [`CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.FormalODModule.exists_sum_linearPart_varpi_smul_eq_subst_varpi_add_addCoboundary
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (N : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k) (hΓ : ∀ l, X₀.F.IsSymmTwoCocycle (Γ l))
    (hNΓ : ∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) :
    let pull : (Fin 2 → MvPowerSeries (Fin 2) k) → MvPowerSeries (Fin 2 ⊕ Fin 2) k →
        MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun φ Γ =>
      MvPowerSeries.subst
        (Sum.elim
          (fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inl m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
          fun i => MvPowerSeries.subst
            (fun m => (MvPowerSeries.X (Sum.inr m) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (φ i))
        Γ
    ∃ g : Fin 2 → MvPowerSeries (Fin 2) k, (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
      ∀ l, ∑ i, MvFormalGroup.linearPart X₀.varpi l i • Γ i =
        pull X₀.varpi (Γ l) + X₀.F.addCoboundary (g l) := by sorry
