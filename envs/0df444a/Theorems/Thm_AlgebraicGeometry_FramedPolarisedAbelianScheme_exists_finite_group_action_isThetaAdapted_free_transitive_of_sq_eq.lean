-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_finite_group_action_isThetaAdapted_free_transitive_of_sq_eq
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_finite_group_action_isThetaAdapted_free_transitive_of_sq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/45ea6c45-0028-5232-93a8-82f5eadf13bc
-- title:
--   Finite group acting freely on theta-adapted framings
-- statement:
--   Fix natural numbers $g, N, n$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero and $\prod_i \delta_i = N+1$, a bijection $e$ of $\{0,\dots,N\}$ with $\prod_i \mathbb{Z}/\delta_i$, and assume $n \ge 3$. Let $B$ be a commutative ring in which $n$ and $N+1$ are invertible, and let $\zeta, \omega \in B$ satisfy $\zeta^{N+1} = 1$, $1 - \zeta^{j} \in B^{\times}$ for $0 < j < N+1$, and $\omega^{2} = \zeta$. The assertion is the existence of a finite group $\Gamma$ together with an operation $\mathrm{act}$ that, for every commutative ring $S$ and every morphism $s : \operatorname{Spec} S \to \operatorname{Spec} B$, sends $\gamma \in \Gamma$ and a framed polarised abelian scheme $X$ of type $(g, N, n)$ over $S$ — that is, an abelian scheme $A \to \operatorname{Spec} S$ with commutative relative group law, fibres of dimension $g$, $2g$ sections of exact order dividing $n$ that give a basis of the $n$-torsion of every geometric fibre, an invertible module $\mathrm{pol}$ with geometric fibre $H^{0}$-rank $N+1$, and a frame consisting of $N+1$ global sections of $\mathrm{pol}$ forming a section basis together with the associated closed immersion into $\mathbb{P}^{N}_{S}$ — to another such object, with eight properties. (i) $\mathrm{act}\,\gamma\,X$ has literally the same underlying polarised abelian scheme as $X$, so only the frame is moved. (ii) $\mathrm{act}$ preserves the property $\mathrm{IsThetaAdapted}\ \delta\ e$, namely that there is a Schrödinger frame for $(X.f, X.L, X.\mathrm{pol})$ whose sections, indexed through $e$, are the pullbacks of the frame sections $X.\mathrm{frame}.\sigma$. (iii) $\mathrm{act}\,1\,X$ is isomorphic to $X$ as a framed object (an isomorphism of schemes over $S$ compatible with the group law, the $2g$ sections, the map to $\mathbb{P}^{N}$, and locally with $\mathrm{pol}$). (iv) $\mathrm{act}\,(\gamma\gamma')\,X$ is framed-isomorphic to $\mathrm{act}\,\gamma\,(\mathrm{act}\,\gamma'\,X)$. (v) $\mathrm{act}\,\gamma$ carries framed isomorphisms to framed isomorphisms. (vi) It commutes with base change: if $\varphi : S \to S'$ is a ring homomorphism with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$, and $X'$ over $S'$ is a pullback of $X$ along $\varphi$, then $\mathrm{act}\,\gamma\,X'$ is a pullback of $\mathrm{act}\,\gamma\,X$. (vii) Freeness: over a nontrivial $S$, if $X$ is theta-adapted and $\mathrm{act}\,\gamma\,X$ is framed-isomorphic to $X$, then $\gamma = 1$. (viii) Zariski-local transitivity: if $X, X'$ over $S$ are both theta-adapted and their underlying polarised abelian schemes are isomorphic, then there are finitely many $r_1, \dots, r_m \in S$ generating the unit ideal such that for each $j$ and any pullbacks $Y, Y'$ of $X, X'$ to $S[1/r_j]$ there is $\gamma \in \Gamma$ with $\mathrm{act}\,\gamma\,Y$ framed-isomorphic to $Y'$.
--
--   This is the frame-change action of the finite symplectic-type automorphism group of the Heisenberg group $\mathcal{G}(\delta)$ of level $N+1$ on theta-adapted framings, in the style of Mumford's theory of theta structures; the hypothesis $\omega^{2} = \zeta$ ensures that the relevant characters are available in the base, keeping the group finite and independent of $S$. It is used to pass from a fine moduli space for quasi-projective framed polarised abelian schemes to one for the theta-type condition, by identifying theta-adapted framings of a fixed polarised abelian scheme as a Zariski-local $\Gamma$-orbit with trivial stabilisers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_finite_group_action_isThetaAdapted_free_transitive_of_sq_eq.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_finite_group_action_isThetaAdapted_free_transitive_of_sq_eq
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (hn : 3 ≤ n) (B : Type) [CommRing B] (hn' : IsUnit ((n : ℕ) : B)) (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Fintype Γ)
      (act : ∀ (S : Type) [CommRing S], (Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) → Γ →
        FramedPolarisedAbelianScheme g N n S → FramedPolarisedAbelianScheme g N n S),
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
          (X : FramedPolarisedAbelianScheme g N n S),
          (act S s γ X).toPolarisedAbelianScheme = X.toPolarisedAbelianScheme) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
          (X : FramedPolarisedAbelianScheme g N n S),
          X.IsThetaAdapted δ e → (act S s γ X).IsThetaAdapted δ e) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (X : FramedPolarisedAbelianScheme g N n S),
          FramedPolarisedAbelianScheme.Iso (act S s 1 X) X) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ γ' : Γ)
          (X : FramedPolarisedAbelianScheme g N n S),
          FramedPolarisedAbelianScheme.Iso (act S s (γ * γ') X) (act S s γ (act S s γ' X))) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
          (X X' : FramedPolarisedAbelianScheme g N n S),
          FramedPolarisedAbelianScheme.Iso X X' → FramedPolarisedAbelianScheme.Iso (act S s γ X) (act S s γ X')) ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
          Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
          ∀ (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
          FramedPolarisedAbelianScheme.IsPullback φ X X' → FramedPolarisedAbelianScheme.IsPullback φ (act S s γ X) (act S' s' γ X')) ∧
      (∀ (S : Type) [CommRing S] [Nontrivial S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (γ : Γ)
          (X : FramedPolarisedAbelianScheme g N n S),
          X.IsThetaAdapted δ e → FramedPolarisedAbelianScheme.Iso (act S s γ X) X → γ = 1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (X X' : FramedPolarisedAbelianScheme g N n S),
          X.IsThetaAdapted δ e → X'.IsThetaAdapted δ e →
          PolarisedAbelianScheme.Iso X.toPolarisedAbelianScheme X'.toPolarisedAbelianScheme →
          ∃ (m : ℕ) (r : Fin m → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ (j : Fin m)
            (Y Y' : FramedPolarisedAbelianScheme g N n (Localization.Away (r j))),
            FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X Y →
            FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X' Y' →
            ∃ γ : Γ, FramedPolarisedAbelianScheme.Iso
              (act (Localization.Away (r j)) (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r j)))) ≫ s) γ Y) Y') := by sorry
