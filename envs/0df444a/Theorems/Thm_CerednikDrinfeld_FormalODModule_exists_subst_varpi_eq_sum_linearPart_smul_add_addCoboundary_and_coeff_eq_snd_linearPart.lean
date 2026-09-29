-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_subst_varpi_eq_sum_linearPart_smul_add_addCoboundary_and_coeff_eq_snd_linearPart
-- name    : CerednikDrinfeld.FormalODModule.exists_subst_varpi_eq_sum_linearPart_smul_add_addCoboundary_and_coeff_eq_snd_linearPart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/a9268c59-4004-5249-9efe-3297939b1da5
-- title:
--   First-order varpi-equivariance: cocycle pullback modulo coboundary
-- statement:
--   Let $q$ be a prime, $k$ a field of characteristic $q$, and $j_0 : \mathbb{Z}_q^{(2)} \to k$ a ring homomorphism, where $\mathbb{Z}_q^{(2)} =$ `Zp2 q` is the ring of Witt vectors of the field with $q^2$ elements. Let $X_0$ be a formal $\mathcal O_D$-module over $k$ — a commutative two-dimensional formal group law $F_0$ together with an action of `Zp2 q` by law endomorphisms and a uniformiser series $\varpi_0 =$ `X₀.varpi` satisfying $\varpi_0\circ\varpi_0 = [q]$ and $\varpi_0\circ[a] = [\varphi(a)]\circ\varpi_0$ — which is special for $j_0$ and of height $4$. Let $N$ be a formal $\mathcal O_D$-module over the dual numbers $k[\varepsilon]$ whose push-forward along the projection $k[\varepsilon]\to k$ equals, on the nose, the formal $\mathcal O_D$-module underlying $X_0$. Let $\Gamma = (\Gamma_1,\Gamma_2)$ be power series in two blocks of two variables, each a symmetric normalised two-cocycle for $F_0$ (constant term zero, invariant under interchanging the two blocks, and satisfying the cocycle identity), and assume that the group law of $N$ is the translate obtained by substituting the image of $F_0$ in the first block and $\varepsilon$ times the image of $\Gamma$ in the second block into the image of $F_0$. Writing $\mathrm{pull}\,\phi\,\Gamma$ for $\Gamma(\phi(X),\phi(Y))$, the conclusion asserts the existence of a pair $g = (g_1,g_2)$ of power series in two variables with zero constant term such that for each $l$, $$\Gamma_l(\varpi_0 X,\varpi_0 Y) = \sum_i \lambda(\varpi_0)_{li}\,\Gamma_i + \bigl(g_l(F_0(X,Y)) - g_l(X) - g_l(Y)\bigr),$$ where $\lambda =$ [`MvFormalGroup.linearPart`](def/MvFormalGroup_BasicV2.html#L359) is the matrix of coefficients of the linear terms, and such that for all $l,m$ the coefficient of $X_m$ in $g_l$ is the $\varepsilon$-component of $\lambda(N.\mathrm{varpi})_{lm}$.
--
--   This is the first-order (tangent-level) equivariance computation for deformations of a special formal $\mathcal O_D$-module of height $4$: it converts the $\varpi$-equivariance of a deformation over $k[\varepsilon]$ into the statement that the pullback of the deformation cocycle along $\varpi_0$ agrees with its linear twist up to an explicit coboundary, whose linear part reads off the $\varepsilon$-part of the linear part of the uniformiser of the deformation. It is used in [`CerednikDrinfeld.SpecialFormalODModule.exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq), which produces an isomorphism of deformations reducing to the identity when the linear part of the uniformiser is prescribed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_subst_varpi_eq_sum_linearPart_smul_add_addCoboundary_and_coeff_eq_snd_linearPart.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_subst_varpi_eq_sum_linearPart_smul_add_addCoboundary_and_coeff_eq_snd_linearPart
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
      (∀ l, pull X₀.varpi (Γ l) =
        ∑ i, MvFormalGroup.linearPart X₀.varpi l i • Γ i + X₀.F.addCoboundary (g l)) ∧
      (∀ l m, MvPowerSeries.coeff (Finsupp.single m 1) (g l) =
        TrivSqZeroExt.snd (MvFormalGroup.linearPart N.varpi l m)) := by sorry
