-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/0252590b-e06a-59b2-8943-b988f68c96f8
-- title:
--   Formal mathcal O_D-module homomorphisms from natural maps on nilpotent points
-- statement:
--   Let $p$ be a prime, $L$ a commutative ring, and let $X$, $X'$ be formal $\mathcal O_D$-modules over $L$ in the sense of the project: each consists of a $2$-dimensional formal group law $F$ over $L$ (a pair of power series in $\mathrm{Fin}\,2 \oplus \mathrm{Fin}\,2$ variables with the usual normalisation and associativity), a commutativity hypothesis on $F$, an action `act` of $\mathbb Z_{p^2} = W(\mathbb F_{p^2})$ and a further pair of series `varpi`, all of these being endomorphisms of the law $F$, with `act 1` the identity, `act` multiplicative and additive (the latter via $F$) in its argument, `varpi` composed with itself equal to `act` at $p$, and `varpi` composed with `act a` equal to `act` at the Frobenius of $a$ composed with `varpi`. Suppose given, for every commutative $L$-algebra $C$ (in the same universe) and every ideal $J \subseteq C$, a map $t_{C,J} : C^2 \to C^2$, subject to the following requirements for nilpotent $J$ and arguments with all coordinates in $J$: the values of $t_{C,J}$ again have all coordinates in $J$; $t$ is natural along $L$-algebra maps $\varphi : C \to C'$ carrying $J$ into a nilpotent ideal $J'$; $t_{C,J}$ is additive in the sense that its value at the $J$-adic evaluation of $X.F$ at a pair $(x,y)$ is the $J$-adic evaluation of $X'.F$ at $(t_{C,J}x, t_{C,J}y)$; and $t_{C,J}$ intertwines the $J$-adic evaluations of `X.act a` with those of `X'.act a` for every $a \in \mathbb Z_{p^2}$, and likewise those of `X.varpi` with those of `X'.varpi`. Then there is a unique homomorphism $u : X \to X'$ of formal $\mathcal O_D$-modules, i.e. a pair of power series with zero constant terms which is a homomorphism from $X.F$ to $X'.F$ and commutes by substitution with the actions and with `varpi`, such that for every such $C$, every nilpotent ideal $J$, every $x$ with coordinates in $J$ and every index $i$, the $i$-th coordinate of $t_{C,J}x$ equals the $J$-adic evaluation of the $i$-th component of $u$ at $x$.
--
--   This is the full faithfulness of the functor of points with coordinates in nilpotent ideals, on formal $\mathcal O_D$-modules of dimension $2$ over a fixed base: it is the mechanism by which homomorphisms of formal $\mathcal O_D$-modules are manufactured from maps defined functorially on infinitesimal points. It is obtained from the corresponding statement for bare formal group laws, [`MvFormalGroup.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent`](thm.html#MvFormalGroup.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent), by checking that the resulting law homomorphism commutes with the $\mathbb Z_{p^2}$-action and with $\varpi$, and it feeds the variant in which the nilpotency requirement is relaxed using a density argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
    {p : ℕ} [Fact p.Prime] {L : Type u} [CommRing L] (X X' : CerednikDrinfeld.FormalODModule p L)
    (t : ∀ (C : Type u) [CommRing C] [Algebra L C], Ideal C → (Fin 2 → C) → (Fin 2 → C))
    (ht_mem : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, t C J x i ∈ J)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra L C] [CommRing C'] [Algebra L C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[L] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → t C' J' (φ ∘ x) = φ ∘ t C J x)
    (ht_add : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin 2 → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (X.F.toPowerSeries i)) =
          fun i => MvFormalGroup.adicEval J (Sum.elim (t C J x) (t C J y)) (X'.F.toPowerSeries i))
    (ht_act : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ (a : CerednikDrinfeld.Zp2 p) (x : Fin 2 → C), (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x (X.act a i)) =
          fun i => MvFormalGroup.adicEval J (t C J x) (X'.act a i))
    (ht_varpi : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x (X.varpi i)) =
          fun i => MvFormalGroup.adicEval J (t C J x) (X'.varpi i)) :
    ∃! u : X.Hom X',
      ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
          ∀ i, t C J x i = MvFormalGroup.adicEval J x (u.toSeries i) := by sorry
