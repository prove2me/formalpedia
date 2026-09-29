-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_of_subgroup_ideal
-- name    : CerednikDrinfeld.FormalODModule.exists_hopfAlgebra_ker_eq_of_subgroup_ideal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/e0bbbae5-b411-50e0-be30-7ffd025977f0
-- title:
--   Quotient by a finite free subgroup ideal is a Hopf algebra
-- statement:
--   Fix a prime $p$, a commutative ring $B$, a formal $\mathcal O_D$-module $X$ over $B$ in the sense of the structure `FormalODModule` (a two-dimensional commutative formal group law $F = X.F$ over $B$, an action of $\mathbb{Z}_{p^2}$ by law endomorphisms and a series $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$), and an ideal $I$ of $B[\![x_1,x_2]\!] =$ `MvPowerSeries (Fin 2) B`; only the law $F$ of $X$ occurs in what follows. Assume: $B[\![x]\!]/I$ is finite and free as a $B$-module; there is $q$ with $x_i^{q} \in I$ for both $i$; every $f \in I$ has vanishing constant coefficient; and for every $f \in I$ the series $f(F(x,y))$, obtained by substituting the two components of $F$ into $f$, lies in the ideal of $B[\![x,y]\!]$ spanned by the union of the image of $I$ under substitution of the left-hand variables and its image under substitution of the right-hand variables. Then there exist a commutative ring $L$ carrying a cocommutative Hopf algebra structure over $B$, free and finite as a $B$-module, and a surjective $B$-algebra map $\pi : B[\![x]\!] \to L$ with $\ker \pi = I$, such that each $\pi(x_i)$ is nilpotent; $\pi(G)$ equals the evaluation [`MvFormalGroup.adicEval`](def/MvFormalGroup_PointsV2.html#L20) of $G$ at the points $\pi(x_i)$ with respect to the zero ideal of $L$, for every $G$; the comultiplication of $\pi(x_i)$ equals the corresponding evaluation of $F_i$ in $L \otimes_B L$ at $\pi(x_j) \otimes 1$ and $1 \otimes \pi(x_j)$; the counit kills each $\pi(x_i)$; and the counit of $\pi(G)$ is the constant coefficient of $G$.
--
--   This is the formal-group form of the statement that a finite flat infinitesimal subgroup of a commutative formal group law is a subgroup scheme: the quotient of the power series ring by a subgroup ideal carries a finite free commutative and cocommutative Hopf algebra structure whose comultiplication is induced by the group law and whose counit is the constant term, the antipode coming from the fact that a finite flat submonoid of a group is a subgroup. It is used in the study of invariants and of the $\mathcal O_D$-action on such quotients, in [`CerednikDrinfeld.FormalODModule.act_pow_mem_span_of_isODHom_of_hasKernelOfDegree`](thm.html#CerednikDrinfeld.FormalODModule.act_pow_mem_span_of_isODHom_of_hasKernelOfDegree) and [`CerednikDrinfeld.FormalODModule.eq_span_setOf_invariant_of_subgroup_ideal_of_free`](thm.html#CerednikDrinfeld.FormalODModule.eq_span_setOf_invariant_of_subgroup_ideal_of_free).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_of_subgroup_ideal.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem CerednikDrinfeld.FormalODModule.exists_hopfAlgebra_ker_eq_of_subgroup_ideal
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hfree : Module.Free B (MvPowerSeries (Fin 2) B ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)))) :
    ∃ (L : Type) (_ : CommRing L) (_ : HopfAlgebra B L) (_ : Coalgebra.IsCocomm B L)
      (_ : Module.Free B L) (_ : Module.Finite B L) (π : MvPowerSeries (Fin 2) B →ₐ[B] L),
      Function.Surjective π ∧
      RingHom.ker π = I ∧
      (∀ i, IsNilpotent (π (MvPowerSeries.X i))) ∧
      (∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G) ∧
      (∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (X.F.toPowerSeries i)) ∧
      (∀ i, Coalgebra.counit (R := B) (π (MvPowerSeries.X i)) = 0) ∧
      (∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G) := by sorry
