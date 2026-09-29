-- Prove2me | Theorems.Thm_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat
-- name    : AdicCompletion.exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/a26ac469-72db-5b00-81ad-1ecfd21a3b51
-- title:
--   Base change of a completed power-series chart along A₀ → A
-- statement:
--   Let $A_0$ and $A$ be discrete valuation rings with $A$ an $A_0$-algebra via a local, injective structure map, and assume the residue field of $A_0$ is perfect. Let $B_0$ be a finite-type, flat $A_0$-algebra, $\mathfrak m_0 \subset B_0$ a maximal ideal, and $W_0$ a local ring, complete with respect to its maximal ideal, with an $A_0$-algebra structure such that $\mathfrak m_{W_0} = \mathfrak m_{A_0} W_0$. Assume given $g_0 \in W_0[[X_0,X_1]]$ and a ring isomorphism $e_0$ from the $\mathfrak m_0$-adic completion of $B_0$ onto $W_0[[X_0,X_1]]/(g_0)$ carrying the image of each $a \in A_0$ to the constant power series on $a$; a ring map $\psi : W_0 \to \hat A$, where $\hat A$ is the $\mathfrak m_A$-adic completion of $A$, compatible with $A_0 \to A \to \hat A$; and a ring map $\chi : B_0 \to \kappa = \mathrm{ResidueField}\,A$ compatible with $A_0 \to A \to \kappa$ and satisfying: whenever $b \in B_0$ and $w \in W_0$ are such that $e_0(b) - \bar w$ lies in the image of $(X_0, X_1) + \mathfrak m_{W_0}W_0[[X_0,X_1]]$ in the quotient, there is $a \in A$ with residue $\chi(b)$ and with $\psi(w) - a \in \mathfrak m_A \hat A$. Put $B = A \otimes_{A_0} B_0$, let $ev : B \to \kappa$ be the ring map induced by $A \to \kappa$ and $\chi$, and $\mathfrak m = \ker ev$. Then $\mathfrak m$ is maximal and there is a ring isomorphism $e$ from the $\mathfrak m$-adic completion of $B$ onto $\hat A[[X_0,X_1]]/(\psi_* g_0)$ which sends the image of each $a \in A$ to the class of the constant series on the image of $a$ in $\hat A$, and which sends the image of $1 \otimes b$ to the class of $\psi_* s$ whenever $e_0(b)$ is the class of $s \in W_0[[X_0,X_1]]$.
--
--   This is the assertion that a two-variable power-series presentation of a completed local ring of a flat finite-type algebra propagates under base change along a local (possibly ramified, possibly non-finite) map of discrete valuation rings, at a point rational over the larger residue field. It is used to transport power-series charts on modular curves, in the form of completed local rings of Drinfeld charts, to base-changed situations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing TensorProduct MvPowerSeries

theorem AdicCompletion.exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat
    (A₀ A : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    [PerfectField (ResidueField A₀)]
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.FiniteType A₀ B₀] [Module.Flat A₀ B₀]
    (𝔪₀ : Ideal B₀) [𝔪₀.IsMaximal]
    (W₀ : Type) [CommRing W₀] [IsLocalRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀] [Algebra A₀ W₀]

    (hW₀ : maximalIdeal W₀ = (maximalIdeal A₀).map (algebraMap A₀ W₀))
    (g₀ : MvPowerSeries (Fin 2) W₀)
    (e₀ : AdicCompletion 𝔪₀ B₀ ≃+* MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀})
    (he₀ : ∀ a : A₀, e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) (algebraMap A₀ B₀ a)) =
      Ideal.Quotient.mk (Ideal.span {g₀}) (C (algebraMap A₀ W₀ a)))
    (ψ : W₀ →+* AdicCompletion (maximalIdeal A) A)
    (hψ : ∀ a : A₀, ψ (algebraMap A₀ W₀ a) = algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap A₀ A a))
    (χ : B₀ →+* ResidueField A)
    (hχA₀ : ∀ a : A₀, χ (algebraMap A₀ B₀ a) = IsLocalRing.residue A (algebraMap A₀ A a))
    (hχ : ∀ (b : B₀) (w : W₀),
      e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b) - Ideal.Quotient.mk (Ideal.span {g₀}) (C w) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} ⊔ (maximalIdeal W₀).map (C : W₀ →+* MvPowerSeries (Fin 2) W₀)).map
          (Ideal.Quotient.mk (Ideal.span {g₀})) →
      ∃ a : A, IsLocalRing.residue A a = χ b ∧
        ψ w - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
          (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    let Â := AdicCompletion (maximalIdeal A) A
    let B := A ⊗[A₀] B₀
    let ev : B →+* ResidueField A :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A₀ A (ResidueField A))
        ({ toRingHom := χ, commutes' := fun a => by
            rw [IsScalarTower.algebraMap_apply A₀ A (ResidueField A)]; exact hχA₀ a } : B₀ →ₐ[A₀] ResidueField A)
        (fun _ _ => Commute.all _ _)).toRingHom
    let 𝔪 : Ideal B := RingHom.ker ev
    ∃ (_ : 𝔪.IsMaximal)
      (e : AdicCompletion 𝔪 B ≃+* MvPowerSeries (Fin 2) Â ⧸ Ideal.span {MvPowerSeries.map ψ g₀}),
      (∀ a : A, e (algebraMap B (AdicCompletion 𝔪 B) (algebraMap A B a)) =
        Ideal.Quotient.mk _ (C (algebraMap A Â a))) ∧
      (∀ (b : B₀) (s : MvPowerSeries (Fin 2) W₀),
        e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b) = Ideal.Quotient.mk (Ideal.span {g₀}) s →
        e (algebraMap B (AdicCompletion 𝔪 B) ((1 : A) ⊗ₜ[A₀] b)) =
          Ideal.Quotient.mk _ (MvPowerSeries.map ψ s)) := by sorry
