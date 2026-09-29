-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_AlgFunctor_formalQuotient_descent
-- name    : CerednikDrinfeld.FormalOmega.AlgFunctor.formalQuotient_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/28bb666a-c1ed-5149-8b31-042b69579601
-- title:
--   Descent of a formal categorical quotient through p
-- statement:
--   Fix a commutative ring $\mathcal O$ and an element $\pi \in \mathcal O$, and let $F$ be an object of `AlgFunctor 𝒪`, that is, an assignment $B \mapsto F.\mathrm{obj}\,B$ of a type to each commutative $\mathcal O$-algebra $B$ together with maps $F.\mathrm{map}\,\varphi : F.\mathrm{obj}\,B \to F.\mathrm{obj}\,B'$ for $\mathcal O$-algebra homomorphisms $\varphi : B \to B'$, compatible with identities and composition.
--
--   **Action data.** Let $\Gamma$ be a group and let `act` assign to each $\mathcal O$-algebra $B$, each $\gamma \in \Gamma$ and each pair $x, x' \in F.\mathrm{obj}\,B$ a proposition, thought of as '$x' = \gamma x$'. Five hypotheses constrain this relation: `hact_fun` (functionality: if $x'$ and $x''$ are both related to $x$ by $\gamma$ then $x' = x''$), `hact_total` (totality: every $x$ is related by every $\gamma$ to some $x'$), `hact_one` (the identity of $\Gamma$ relates every $x$ to itself), `hact_mul` (if $\gamma$ relates $x$ to $y$ and $\gamma'$ relates $y$ to $z$, then $\gamma'\gamma$ relates $x$ to $z$) and `hact_nat` (naturality: if $\gamma$ relates $x$ to $x'$ in $F.\mathrm{obj}\,B$, then $\gamma$ relates $F.\mathrm{map}\,\varphi\,x$ to $F.\mathrm{map}\,\varphi\,x'$ for every $\mathcal O$-algebra homomorphism $\varphi : B \to B'$). A subgroup $\Gamma' \le \Gamma$ is given.
--
--   **Geometric data.** Let $\mathcal X'$ and $\mathcal X$ be schemes with structure morphisms $f' : \mathcal X' \to \operatorname{Spec} \mathcal O$ and $f : \mathcal X \to \operatorname{Spec} \mathcal O$, and let $p : \mathcal X' \to \mathcal X$ satisfy $p$ followed by $f$ equals $f'$ (hypothesis `hp`). A family $a : \Gamma \to (\mathcal X' \to \mathcal X')$ of endomorphisms is given, subject to: `ha_over` ($a\,\gamma$ followed by $f'$ is $f'$, i.e. each $a\,\gamma$ is a morphism over $\mathcal O$), `ha_p` ($a\,\gamma$ followed by $p$ is $p$, i.e. each $a\,\gamma$ lies over $\mathcal X$), `ha_one` ($a\,\gamma = \mathrm{id}_{\mathcal X'}$ for every $\gamma \in \Gamma'$) and `ha_mul` ($a(\gamma'\gamma) = a\,\gamma$ followed by $a\,\gamma'$).
--
--   For a morphism $g : Y \to \operatorname{Spec} \mathcal O$, the functor `Scheme.nilpPoints g` sends an $\mathcal O$-algebra $B$ to the set of morphisms $\operatorname{Spec} B \to Y$ whose composite with $g$ is the structure morphism $\operatorname{Spec} B \to \operatorname{Spec} \mathcal O$, with functoriality by precomposition with $\operatorname{Spec}$ of an $\mathcal O$-algebra map; for a morphism $h : X \to Y$ over $\operatorname{Spec} \mathcal O$, `Scheme.nilpPoints.mapHom` is the induced natural transformation, postcomposition with $h$. Throughout, 'family' means a collection of maps indexed by the $\mathcal O$-algebras $B$ in which $\pi$ becomes nilpotent (the argument `IsNilpotent (algebraMap 𝒪 B π)`), and 'natural' means commuting with the transition maps along every $\mathcal O$-algebra homomorphism $\varphi : B \to B'$ between two such algebras.
--
--   **Hypothesis `hp_univ`: $p$ is a formal categorical quotient of $\mathcal X'$ by $a(\Gamma)$.** For every scheme $T$ with $t : T \to \operatorname{Spec} \mathcal O$ and every family $\rho$ of maps from the $\mathcal O$-points of $f'$ to those of $t$ which is natural and invariant under the action, i.e. $\rho(y \mathbin{\text{followed by}} a\,\gamma) = \rho(y)$ for all $\gamma \in \Gamma$, there exists a family $u$ of maps from the points of $f$ to those of $t$ such that: $u$ is natural; $u(y \mathbin{\text{followed by}} p) = \rho(y)$ for all $y$; and any natural family $u'$ with $u'(y \mathbin{\text{followed by}} p) = \rho(y)$ agrees with $u$ on every point of $f$ over every such $B$.
--
--   **Hypothesis on $\Theta'$.** A family $\Theta'$ is given, taking $x \in F.\mathrm{obj}\,B$ to a point of $f'$ over $B$, subject to three conditions: `hΘ'_nat` ($\Theta'$ is natural); `hΘ'_eqv` (equivariance: if $\gamma$ relates $x$ to $x'$, then $\Theta'(x')$ is $\Theta'(x)$ followed by $a\,\gamma$); and `hΘ'_univ` ($\Theta'$ is a formal categorical quotient of $F$ by $\Gamma'$): for every $T$, $t : T \to \operatorname{Spec} \mathcal O$ and every natural family $\rho$ from $F$ to the points of $t$ which is $\Gamma'$-invariant — $\rho(x') = \rho(x)$ whenever $\gamma \in \Gamma'$ relates $x$ to $x'$ — there is a natural family $u$ from the points of $f'$ to those of $t$ with $u \circ \Theta' = \rho$, and any natural family $u'$ with $u' \circ \Theta' = \rho$ agrees with $u$ pointwise.
--
--   **Conclusion.** Put $\Theta(x) := \Theta'(x)$ followed by $p$, i.e. the composite of $\Theta'$ with the natural transformation induced by $p$. Then three assertions hold.
--
--   (i) $\Theta$ is natural: $\Theta(F.\mathrm{map}\,\varphi\,x)$ equals the image of $\Theta(x)$ under the transition map of `Scheme.nilpPoints f` along $\varphi$, for all $\mathcal O$-algebras $B, B'$ in which $\pi$ is nilpotent, all $\varphi : B \to B'$ and all $x \in F.\mathrm{obj}\,B$.
--
--   (ii) $\Theta$ is $\Gamma$-invariant: if $\gamma \in \Gamma$ relates $x$ to $x'$ in $F.\mathrm{obj}\,B$, then $\Theta(x') = \Theta(x)$ — invariance now for the whole of $\Gamma$, not merely $\Gamma'$.
--
--   (iii) $\Theta$ is a formal categorical quotient of $F$ by $\Gamma$: for every scheme $T$, every $t : T \to \operatorname{Spec} \mathcal O$ and every family $\rho$ of maps $F.\mathrm{obj}\,B \to$ (points of $t$ over $B$) which is natural and $\Gamma$-invariant ($\rho(x') = \rho(x)$ whenever some $\gamma \in \Gamma$ relates $x$ to $x'$), there exists a family $u$ of maps from the points of $f$ over $B$ to the points of $t$ over $B$ such that $u$ is natural; $u(\Theta(x)) = \rho(x)$ for all $B$ with $\pi$ nilpotent and all $x \in F.\mathrm{obj}\,B$; and for every family $u'$ of the same shape which is natural and satisfies $u'(\Theta(x)) = \rho(x)$, one has $u'(z) = u(z)$ for every point $z$ of $f$ over every such $B$.
--
--   This is the functorial bookkeeping step in the Čerednik–Drinfeld uniformisation at a level where the uniformising group has torsion: a formal categorical quotient of the functor $F$ by a subgroup $\Gamma'$, realised by a fine object $\mathcal X'$, is pushed forward along a morphism $p$ which is itself a formal categorical quotient of $\mathcal X'$ by the induced action of $\Gamma$, yielding a formal categorical quotient of $F$ by all of $\Gamma$ on $\pi$-nilpotent algebras. It is used in the construction of the Čerednik–Drinfeld uniformisation for coarse and for fine moduli problems of quaternionic type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_AlgFunctor_formalQuotient_descent.lean

import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.AlgFunctor.formalQuotient_descent
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)

    (Γ : Type) [Group Γ] (act : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → F.obj B → F.obj B → Prop)
    (hact_fun : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (x x' x'' : F.obj B), act B γ x x' → act B γ x x'' → x' = x'')
    (hact_total : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (x : F.obj B), ∃ x', act B γ x x')
    (hact_one : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : F.obj B), act B 1 x x)
    (hact_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ γ' : Γ) (x y z : F.obj B), act B γ x y → act B γ' y z → act B (γ' * γ) x z)
    (hact_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (γ : Γ)
      (x x' : F.obj B), act B γ x x' → act B' γ (F.map φ x) (F.map φ x'))
    (Γ' : Subgroup Γ)

    (𝒳' 𝒳 : Scheme.{0}) (f' : 𝒳' ⟶ Spec (CommRingCat.of 𝒪)) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (p : 𝒳' ⟶ 𝒳) (hp : p ≫ f = f')
    (a : Γ → (𝒳' ⟶ 𝒳')) (ha_over : ∀ γ, a γ ≫ f' = f') (ha_p : ∀ γ, a γ ≫ p = p) (ha_one : ∀ γ ∈ Γ', a γ = 𝟙 𝒳')
    (ha_mul : ∀ γ γ' : Γ, a (γ' * γ) = a γ ≫ a γ')

    (hp_univ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f').obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f').obj B), ρ B' hB' ((Scheme.nilpPoints f').map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (y : (Scheme.nilpPoints f').obj B),
        ρ B hB ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B y) = ρ B hB y) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B),
          u B hB ((Scheme.nilpPoints.mapHom f' f p hp).app B y) = ρ B hB y) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B),
            u' B hB ((Scheme.nilpPoints.mapHom f' f p hp).app B y) = ρ B hB y) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = u B hB z)

    (Θ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints f').obj B)
    (hΘ'_nat : (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), Θ' B' hB' (F.map φ x) = (Scheme.nilpPoints f').map φ (Θ' B hB x)))
    (hΘ'_eqv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B), act B γ x x' →
      Θ' B hB x' = (Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B (Θ' B hB x))
    (hΘ'_univ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), ρ B' hB' (F.map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ), γ ∈ Γ' → ∀ x x' : F.obj B, act B γ x x' → ρ B hB x' = ρ B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f').obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f').obj B), u B' hB' ((Scheme.nilpPoints f').map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u B hB (Θ' B hB x) = ρ B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f').obj B → (Scheme.nilpPoints t).obj B, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f').obj B), u' B' hB' ((Scheme.nilpPoints f').map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u' B hB (Θ' B hB x) = ρ B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B), u' B hB y = u B hB y)
    :

    let Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints f).obj B := fun B _ _ hB x => (Scheme.nilpPoints.mapHom f' f p hp).app B (Θ' B hB x)
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), Θ B' hB' (F.map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x)) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B), act B γ x x' → Θ B hB x' = Θ B hB x) ∧
    (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), ρ B' hB' (F.map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B), act B γ x x' → ρ B hB x' = ρ B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u B hB (Θ B hB x) = ρ B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u' B hB (Θ B hB x) = ρ B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = u B hB z) := by sorry
