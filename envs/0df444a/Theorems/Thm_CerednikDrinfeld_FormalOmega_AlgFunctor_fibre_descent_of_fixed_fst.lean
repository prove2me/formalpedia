-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_AlgFunctor_fibre_descent_of_fixed_fst
-- name    : CerednikDrinfeld.FormalOmega.AlgFunctor.fibre_descent_of_fixed_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/85f3fac5-7807-5a0c-981e-445019466193
-- title:
--   Descent of fixed-coefficient geometric fibres along a Γ-quotient
-- statement:
--   Let $\mathcal O$ be a commutative ring, $\pi \in \mathcal O$, and let $C$, $G$ be functors on $\mathcal O$-algebras in the sense of `AlgFunctor` (an assignment $B \mapsto C.obj\,B$ of a type to each $\mathcal O$-algebra together with functorial transport along $\mathcal O$-algebra maps). Let $\Gamma$ be a group, let `cact` give for each $\mathcal O$-algebra $B$ an action-like function $\Gamma \times C.obj\,B \to C.obj\,B$ satisfying $\mathrm{cact}(\gamma'\gamma)c = \mathrm{cact}\,\gamma'(\mathrm{cact}\,\gamma\,c)$, and let `gact` give for each $B$ a $\Gamma$-indexed relation on $G.obj\,B$ that is total (every $\gamma, x$ admit some $x'$ with $\mathrm{gact}\,\gamma\,x\,x'$) and multiplicative ($\mathrm{gact}\,\gamma\,x\,y$ and $\mathrm{gact}\,\gamma'\,y\,z$ give $\mathrm{gact}(\gamma'\gamma)x\,z$); let $\Gamma' \le \Gamma$ be a subgroup. Let $\mathcal X', \mathcal X$ be schemes with structure morphisms $f' , f$ to $\operatorname{Spec}\mathcal O$, let $p : \mathcal X' \to \mathcal X$ satisfy $f' = f \circ p$, and let $a : \Gamma \to \operatorname{End}(\mathcal X')$ have $f' \circ a\gamma = f'$ and $p \circ a\gamma = p$. For an $\mathcal O$-algebra $B$ write $\mathcal X'(B)$ for the $\mathcal O$-morphisms $\operatorname{Spec}B \to \mathcal X'$ (the type `Scheme.nilpPoints f'` assigns to $B$), on which `mapHom` acts by postcomposition. Assume: for every algebraically closed $\mathcal O$-field $k$ in which $\pi$ has nilpotent image, postcomposition with $p$ is surjective $\mathcal X'(k) \to \mathcal X(k)$ and identifies $y, y'$ exactly when $y' = (a\gamma) \circ y$ for some $\gamma \in \Gamma$; a map $\Theta'$ sending, for each $\mathcal O$-algebra $B$ with $\pi$ nilpotent, a pair in $C.obj\,B \times G.obj\,B$ to a point of $\mathcal X'(B)$, equivariant in the sense that $\mathrm{gact}\,\gamma\,x\,x'$ implies $\Theta'(\mathrm{cact}\,\gamma\,c, x') = (a\gamma) \circ \Theta'(c,x)$; a relation `ceq` on $C.obj\,k$ for each such $k$ such that for fixed $c$ the map $x \mapsto \Theta'(c,x)$ is onto $\mathcal X'(k)$ and $\Theta'(c,x) = \Theta'(c',x')$ implies the existence of $\gamma \in \Gamma'$ with $\mathrm{ceq}(\mathrm{cact}\,\gamma\,c)\,c'$ and $\mathrm{gact}\,\gamma\,x\,x'$; and a lifting hypothesis: $\mathrm{ceq}(\mathrm{cact}\,\gamma\,c)\,c$ implies the existence of $z \in \Gamma$ with $\mathrm{cact}(z\gamma)c = c$ and $\mathrm{gact}\,z\,x\,x$ for all $x$. Then, setting $\Theta := p \circ \Theta'$, for every algebraically closed $\mathcal O$-field $k$ with $\pi$ nilpotent and every fixed $c \in C.obj\,k$: $x \mapsto \Theta(c,x)$ is onto $\mathcal X(k)$, and $\Theta(c,x) = \Theta(c,x')$ holds if and only if there is $\gamma \in \Gamma$ with $\mathrm{cact}\,\gamma\,c = c$ and $\mathrm{gact}\,\gamma\,x\,x'$. The $\gamma$ produced in the conclusion carries no constraint of lying in $\Gamma'$.
--
--   This is the descent step in the Čerednik–Drinfeld comparison: a fixed-coefficient surjectivity-and-fibre description of a parametrisation $\Theta'$ of the nilpotent-points functor of a fine object $\mathcal X'$ is transported along a quotient map $p : \mathcal X' \to \mathcal X$ whose geometric fibres over the special fibre are the $a(\Gamma)$-orbits. It feeds the existence theorem for the Čerednik–Drinfeld uniformization of quaternionic curves, [`CerednikDrinfeld.QM.IsCoarseModuli.exists_cerednikDrinfeld_uniformization_of_span_eq_of_geometricallyConnected_of_squarefree_of_isUnit_two_of_geometricallyConnected_tower_of_isUnit_three`](thm.html#CerednikDrinfeld.QM.IsCoarseModuli.exists_cerednikDrinfeld_uniformization_of_span_eq_of_geometricallyConnected_of_squarefree_of_isUnit_two_of_geometricallyConnected_tower_of_isUnit_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_AlgFunctor_fibre_descent_of_fixed_fst.lean

import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.AlgFunctor.fibre_descent_of_fixed_fst
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (C G : AlgFunctor 𝒪)

    (Γ : Type) [Group Γ]
    (cact : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → C.obj B → C.obj B)
    (gact : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → G.obj B → G.obj B → Prop)
    (hcact_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ γ' : Γ) (c : C.obj B), cact B (γ' * γ) c = cact B γ' (cact B γ c))
    (hgact_total : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (x : G.obj B), ∃ x', gact B γ x x')
    (hgact_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ γ' : Γ) (x y z : G.obj B), gact B γ x y → gact B γ' y z → gact B (γ' * γ) x z)
    (Γ' : Subgroup Γ)

    (𝒳' 𝒳 : Scheme.{0}) (f' : 𝒳' ⟶ Spec (CommRingCat.of 𝒪)) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (p : 𝒳' ⟶ 𝒳) (hp : p ≫ f = f')
    (a : Γ → (𝒳' ⟶ 𝒳')) (ha_over : ∀ γ, a γ ≫ f' = f') (ha_p : ∀ γ, a γ ≫ p = p)

    (hp_geom : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)),
      Function.Surjective ((Scheme.nilpPoints.mapHom f' f p hp).app k) ∧
      ∀ y y' : (Scheme.nilpPoints f').obj k, (Scheme.nilpPoints.mapHom f' f p hp).app k y = (Scheme.nilpPoints.mapHom f' f p hp).app k y' ↔
        ∃ γ : Γ, y' = (Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app k y)

    (Θ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod C G).obj B → (Scheme.nilpPoints f').obj B)
    (hΘ'_eqv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (c : C.obj B) (x x' : G.obj B),
      gact B γ x x' → Θ' B hB (cact B γ c, x') = (Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B (Θ' B hB (c, x)))

    (ceq : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k], C.obj k → C.obj k → Prop)
    (hΘ'_geom : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)),
      (∀ (c : C.obj k) (y : (Scheme.nilpPoints f').obj k), ∃ x : G.obj k, Θ' k hk (c, x) = y) ∧
      ∀ (c c' : C.obj k) (x x' : G.obj k), Θ' k hk (c, x) = Θ' k hk (c', x') → ∃ γ ∈ Γ', ceq k (cact k γ c) c' ∧ gact k γ x x')

    (hlift : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (γ : Γ) (c : C.obj k),
      ceq k (cact k γ c) c → ∃ z : Γ, cact k (z * γ) c = c ∧ ∀ x : G.obj k, gact k z x x)
    :

    let Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod C G).obj B → (Scheme.nilpPoints f).obj B :=
      fun B _ _ hB x => (Scheme.nilpPoints.mapHom f' f p hp).app B (Θ' B hB x)
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (c : C.obj k),
      (∀ y : (Scheme.nilpPoints f).obj k, ∃ x : G.obj k, Θ k hk (c, x) = y) ∧
      ∀ x x' : G.obj k, Θ k hk (c, x) = Θ k hk (c, x') ↔ ∃ γ : Γ, cact k γ c = c ∧ gact k γ x x' := by sorry
