-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/4690d08d-2833-5fba-a1e9-fb0c793c72b7
-- title:
--   Cocycle tuples of first-order mathcal O_D-deformations lie on one line
-- statement:
--   Let $q$ be a prime, let $k$ be an algebraically closed field of characteristic $q$, let $j_0\colon W(\mathbb F_{q^2}) \to k$ be a ring homomorphism, and let $X_0$ be a special formal $\mathcal O_D$-module over $k$ of height $4$ relative to $j_0$: a two-dimensional commutative formal group law $F = X_0.F$ over $k$ together with an action of $W(\mathbb F_{q^2})$ by endomorphisms and an endomorphism $\varpi$ with $\varpi \circ \varpi = [q]$ and $\varpi \circ [a] = [\mathrm{Frob}\,a] \circ \varpi$, satisfying the specialness and height conditions. Assume the smoothness hypothesis: it is *not* the case that the linear part of $\varpi$ (the matrix of degree-one coefficients of the two series of $\varpi$), acting by matrix–vector multiplication, annihilates both the submodule $\mathrm{lieZero}\,j_0$ (the intersection over $a$ of the kernels of $\mathrm{lieAct}\,a - j_0(a)\cdot\mathrm{id}$ on $\mathrm{Lie}\,X_0$) and the submodule $\mathrm{lieOne}\,j_0$ (likewise with $j_0(\mathrm{Frob}\,a)$). Then there is a single tuple $\Gamma_1 = (\Gamma_{1,0},\Gamma_{1,1})$ of series in two blocks of two variables, each a symmetric normalised $2$-cocycle for $F$ (zero constant term, invariant under interchanging the two blocks, and satisfying the cocycle identity), with the following property. For every formal $\mathcal O_D$-module $N$ over the dual numbers $k[\varepsilon]$ whose base change along $k[\varepsilon] \to k$ equals $X_0$ on the nose, and every tuple $\Gamma = (\Gamma_0,\Gamma_1')$ of symmetric $2$-cocycles for $F$ such that the group law of $N$ is literally the translate obtained by substituting $(\iota F_j,\ \varepsilon\,\iota\Gamma_j)_j$ into $\iota F_i$, where $\iota\colon k \to k[\varepsilon]$ is the inclusion, there exist a scalar $c \in k$ and series $g_0, g_1$ in two variables with zero constant term such that $\Gamma_l = c\,\Gamma_{1,l} + \big(g_l(F(X,Y)) - g_l(X) - g_l(Y)\big)$ for $l = 0,1$.
--
--   This is the tangent-space computation for the deformation theory of special formal $\mathcal O_D$-modules underlying the Čerednik–Drinfeld uniformisation: at a point where the linear part of $\varpi$ does not kill both eigenlines of the Lie module, the cocycle tuples classifying first-order deformations of $X_0$ fill out at most one line modulo coboundaries. It is used in [`CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_fin_one_of_not_and`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_fin_one_of_not_and), where this one-dimensionality is converted into a statement about the set of first-order deformations over the dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and.lean

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

theorem CerednikDrinfeld.SpecialFormalODModule.exists_forall_cocycleTuple_eq_smul_add_addCoboundary_of_not_and
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) :
    ∃ Γ₁ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k, (∀ l, X₀.F.IsSymmTwoCocycle (Γ₁ l)) ∧
      ∀ (N : FormalODModule q (DualNumber k)),
        N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule →
      ∀ (Γ : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k), (∀ l, X₀.F.IsSymmTwoCocycle (Γ l)) →
        (∀ i, N.F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (X₀.F.toPowerSeries i))) →
        ∃ (c : k) (g : Fin 2 → MvPowerSeries (Fin 2) k),
          (∀ l, MvPowerSeries.constantCoeff (g l) = 0) ∧
          ∀ l, Γ l = c • Γ₁ l + X₀.F.addCoboundary (g l) := by sorry
