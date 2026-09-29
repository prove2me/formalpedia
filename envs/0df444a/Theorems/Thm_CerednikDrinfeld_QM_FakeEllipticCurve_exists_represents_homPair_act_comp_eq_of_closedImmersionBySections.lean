-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_represents_homPair_act_comp_eq_of_closedImmersionBySections
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_represents_homPair_act_comp_eq_of_closedImmersionBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/59fbb82f-7a59-5edc-b0dd-98dd90a536bb
-- title:
--   Representability of Λ-linear isogeny pairs between fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and a natural number $N$. Fix a family $\beta : \mathrm{Fin}(2\cdot 2) \to \Lambda$ together with the hypothesis `hβ` that every $x \in \Lambda$ is expressible in exactly one way as $\sum_j c_j \beta_j$ with $c : \mathrm{Fin}(2\cdot 2) \to \mathbb{Z}$; thus $\beta$ is a $\mathbb{Z}$-basis of $\Lambda$ indexed by four elements. Fix natural numbers $r,d$, a commutative ring $S$, and two fake elliptic curves $E$ and $A$ of type `FakeEllipticCurve Λ N S`; each such datum consists of a scheme (written `E.A`, `A.A`) with a structure morphism to $\operatorname{Spec} S$ (`E.f`, `A.f`), a commutative relative group law on that morphism (`E.L`, `A.L`), an abelian-scheme property bundle, fibres of topological Krull dimension $2$, an action `E.act` of $\Lambda$ by endomorphisms over $\operatorname{Spec} S$ which is additive, multiplicative and unital for $\Lambda$, compatible with the group law, and subject to the trace condition on tangent spaces at geometric points, together with the remaining level-$N$ data of the structure.
--
--   Assume further given an object $\mathcal{L}_E$ of `E.A.Modules` with `hE₁`: $\mathcal{L}_E$ is invertible, in the sense that each point of `E.A` has an open neighbourhood $U$ over which the pullback of $\mathcal{L}_E$ along $U \hookrightarrow$ `E.A` is isomorphic to the unit sheaf of modules on $U$; and `hE₂`: $\mathcal{L}_E$ admits a closed immersion by sections relative to `E.f`, i.e. for some $M$ there are global sections $\sigma_0,\dots,\sigma_M$ of $\mathcal{L}_E$ and a morphism from `E.A` to $\operatorname{Proj}$ of the graded polynomial ring in $M+1$ variables over $S$, compatible with the projection to $\operatorname{Spec} S$, such that each $\sigma_i$ frames $\mathcal{L}_E$ over the preimage of the basic open set $D(X_i)$ and the sections transform by the coordinate ratios, and such that the morphism to $\operatorname{Proj}$ is a closed immersion. Assume the same two hypotheses `hA₁`, `hA₂` for an object $\mathcal{L}_A$ of `A.A.Modules` relative to `A.f`.
--
--   Under these hypotheses there exist a scheme $X$, a morphism $\pi_X : X \to \operatorname{Spec} S$, and a point rule $\mathrm{pt}$ with the following shape and properties. For a commutative ring $S'$ and a morphism $s : \operatorname{Spec} S' \to \operatorname{Spec} S$, an *isogeny-pair datum over $s$* consists of morphisms $\varphi : E.A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to A.A$ and $\varphi' : A.A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to E.A$ with $\varphi \mathbin{;} A.f$ equal to the second projection followed by $s$ and $\varphi' \mathbin{;} E.f$ equal to the second projection followed by $s$ (the hypotheses $h\varphi$, $h\varphi'$), subject to three further conditions:
--
--   $h_1$ (additivity of $\varphi$): for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $P,Q$ in `SchemeHomOver (t' ≫ s) E.f`, the lift of the product $E.L.\mathrm{mul}\,(t' \mathbin{;} s)\,P\,Q$ and of $t'$ into the fibre product, followed by $\varphi$, coincides with the underlying morphism of $A.L.\mathrm{mul}\,(t' \mathbin{;} s)$ applied to the $\varphi$-images of $P$ and of $Q$;
--
--   $h_2$: the same condition with the roles of $E$ and $A$, and of $\varphi$ and $\varphi'$, interchanged;
--
--   $h_3$: the conjunction of three clauses — first, for each $i$ among the four basis indices, the lift of (first projection followed by $E.\mathrm{act}(\beta_i)$, second projection), followed by $\varphi$, equals $\varphi$ followed by $A.\mathrm{act}(\beta_i)$; second, the corresponding identity for $\varphi'$, with $A.\mathrm{act}(\beta_i)$ and $E.\mathrm{act}(\beta_i)$ exchanged; third, for every proof $hd$ that the image of the natural number $r^d$ in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$, the lift of $\varphi$ and the second projection followed by $\varphi'$ equals the first projection followed by $E.\mathrm{act}\langle r^d, hd\rangle$, and symmetrically the lift of $\varphi'$ and the second projection followed by $\varphi$ equals the first projection followed by $A.\mathrm{act}\langle r^d, hd\rangle$ (so this clause is vacuous when $r^d \notin \Lambda$).
--
--   The rule $\mathrm{pt}$ assigns to each $S'$, each $s$ and each isogeny-pair datum over $s$ an element of `SchemeHomOver s πX`, that is, a morphism $\operatorname{Spec} S' \to X$ whose composite with $\pi_X$ is $s$. The conclusion asserts four things about $X$, $\pi_X$, $\mathrm{pt}$.
--
--   First, naturality: for commutative rings $S'$, $S''$, a ring homomorphism $\psi : S' \to S''$, morphisms $s$ from $\operatorname{Spec} S'$ and $s''$ from $\operatorname{Spec} S''$ to $\operatorname{Spec} S$ with $\operatorname{Spec}(\psi)$ followed by $s$ equal to $s''$, an isogeny-pair datum $(\varphi, h\varphi, \varphi', h\varphi', h_1, h_2, h_3)$ over $s$ and an isogeny-pair datum $(\varphi_2, h\varphi_2, \varphi_2', h\varphi_2', k_1, k_2, k_3)$ over $s''$, if $\varphi_2$ is the base change of $\varphi$ along $\psi$ — namely the lift of the first projection and of the second projection followed by $\operatorname{Spec}(\psi)$, followed by $\varphi$ — and likewise $\varphi_2'$ is the base change of $\varphi'$, then the underlying morphism of $\mathrm{pt}$ applied to the datum over $s''$ equals $\operatorname{Spec}(\psi)$ followed by the underlying morphism of $\mathrm{pt}$ applied to the datum over $s$.
--
--   Second, completeness of the point rule: for every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every $x$ in `SchemeHomOver s πX`, there is an isogeny-pair datum $(\varphi, h\varphi, \varphi', h\varphi', h_1, h_2, h_3)$ over $s$ whose image under $\mathrm{pt}$ is $x$.
--
--   Third, injectivity: for every $S'$, every $s$ and any two isogeny-pair data $(\varphi, h\varphi, \varphi', h\varphi', h_1, h_2, h_3)$ and $(\psi, h\psi, \psi', h\psi', k_1, k_2, k_3)$ over $s$, equality of their images under $\mathrm{pt}$ forces $\varphi = \psi$ and $\varphi' = \psi'$.
--
--   Fourth, $\pi_X$ is separated, locally of finite type and locally of finite presentation.
--
--   Together, the second and third conjuncts say that $\mathrm{pt}$ is a bijection between isogeny-pair data over $s$, up to the proof components of the datum, and the $S'$-points of $X$ over $s$; the first says that this bijection is compatible with base change along ring homomorphisms.
--
--   This is the representability statement for the functor of pairs of $\Lambda$-equivariant homomorphisms between two fake elliptic curves whose composites in both directions are multiplication by $r^d$ — the Hom-scheme construction underlying moduli of isogenies in the Čerednik–Drinfeld part of the development. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_locallyOfFinitePresentation_isSeparated_represents_isIsogenyPair_of_closedImmersionBySections), which packages the same data in the project's isogeny-pair predicate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_represents_homPair_act_comp_eq_of_closedImmersionBySections.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_represents_homPair_act_comp_eq_of_closedImmersionBySections
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j) (r d : ℕ)
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (𝓛E : E.A.Modules) (hE₁ : Scheme.Modules.IsInvertible 𝓛E) (hE₂ : Scheme.Modules.ClosedImmersionBySections 𝓛E E.f)
    (𝓛A : A.A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A) (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A A.f) :
    ∃ (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : Limits.pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
        (φ' : Limits.pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = Limits.pullback.snd A.f s ≫ s),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1) →
        ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ = φ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ (Limits.pullback.snd E.f s) hφ ≫ φ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ' (Limits.pullback.snd A.f s) hφ' ≫ φ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩)) →
          SchemeHomOver s πX),

      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : Limits.pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
          (φ' : Limits.pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = Limits.pullback.snd A.f s ≫ s)
          (h₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ = φ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ (Limits.pullback.snd E.f s) hφ ≫ φ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ' (Limits.pullback.snd A.f s) hφ' ≫ φ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩)))
          (φ₂ : Limits.pullback E.f s'' ⟶ A.A) (hφ₂ : φ₂ ≫ A.f = Limits.pullback.snd E.f s'' ≫ s'')
          (φ₂' : Limits.pullback A.f s'' ⟶ E.A) (hφ₂' : φ₂' ≫ E.f = Limits.pullback.snd A.f s'' ≫ s'')
          (k₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver (t' ≫ s'') E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s'') P Q).1 t' (E.L.mul (t' ≫ s'') P Q).2 ≫ φ₂ =
              (A.L.mul (t' ≫ s'')
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ₂, by rw [Category.assoc, hφ₂, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ₂, by rw [Category.assoc, hφ₂, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (k₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver (t' ≫ s'') A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s'') P Q).1 t' (A.L.mul (t' ≫ s'') P Q).2 ≫ φ₂' =
              (E.L.mul (t' ≫ s'')
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ₂', by rw [Category.assoc, hφ₂', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ₂', by rw [Category.assoc, hφ₂', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (k₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s'' ≫ E.act (β i)) (Limits.pullback.snd E.f s'')
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ₂ = φ₂ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s'' ≫ A.act (β i)) (Limits.pullback.snd A.f s'')
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ₂' = φ₂' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ₂ (Limits.pullback.snd E.f s'') hφ₂ ≫ φ₂' = Limits.pullback.fst E.f s'' ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ₂' (Limits.pullback.snd A.f s'') hφ₂' ≫ φ₂ = Limits.pullback.fst A.f s'' ≫ A.act ⟨_, hd⟩))),
          φ₂ = Limits.pullback.lift (Limits.pullback.fst E.f s'') (Limits.pullback.snd E.f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact Limits.pullback.condition) ≫ φ →
          φ₂' = Limits.pullback.lift (Limits.pullback.fst A.f s'') (Limits.pullback.snd A.f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact Limits.pullback.condition) ≫ φ' →
          (pt S'' s'' φ₂ hφ₂ φ₂' hφ₂' k₁ k₂ k₃).1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ φ' hφ' h₁ h₂ h₃).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πX),
        ∃ (φ : Limits.pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
          (φ' : Limits.pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = Limits.pullback.snd A.f s ≫ s)
          (h₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ = φ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ (Limits.pullback.snd E.f s) hφ ≫ φ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ' (Limits.pullback.snd A.f s) hφ' ≫ φ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩))),
          pt S' s φ hφ φ' hφ' h₁ h₂ h₃ = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ : Limits.pullback E.f s ⟶ A.A) (hφ : φ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
          (φ' : Limits.pullback A.f s ⟶ E.A) (hφ' : φ' ≫ E.f = Limits.pullback.snd A.f s ≫ s)
          (h₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ φ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (h₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ φ = φ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ φ' = φ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift φ (Limits.pullback.snd E.f s) hφ ≫ φ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift φ' (Limits.pullback.snd A.f s) hφ' ≫ φ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩)))
          (ψ : Limits.pullback E.f s ⟶ A.A) (hψ : ψ ≫ A.f = Limits.pullback.snd E.f s ≫ s)
          (ψ' : Limits.pullback A.f s ⟶ E.A) (hψ' : ψ' ≫ E.f = Limits.pullback.snd A.f s ≫ s)
          (k₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) E.f),
            Limits.pullback.lift (E.L.mul (t' ≫ s) P Q).1 t' (E.L.mul (t' ≫ s) P Q).2 ≫ ψ =
              (A.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ ψ, by rw [Category.assoc, hψ, ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ ψ, by rw [Category.assoc, hψ, ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (k₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.f),
            Limits.pullback.lift (A.L.mul (t' ≫ s) P Q).1 t' (A.L.mul (t' ≫ s) P Q).2 ≫ ψ' =
              (E.L.mul (t' ≫ s)
                ⟨Limits.pullback.lift P.1 t' P.2 ≫ ψ', by rw [Category.assoc, hψ', ← Category.assoc, Limits.pullback.lift_snd]⟩
                ⟨Limits.pullback.lift Q.1 t' Q.2 ≫ ψ', by rw [Category.assoc, hψ', ← Category.assoc, Limits.pullback.lift_snd]⟩).1))
          (k₃ : ((∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst E.f s ≫ E.act (β i)) (Limits.pullback.snd E.f s)
                (by rw [Category.assoc, E.act_over]; exact Limits.pullback.condition) ≫ ψ = ψ ≫ A.act (β i)) ∧
            (∀ i : Fin (2 * 2), Limits.pullback.lift (Limits.pullback.fst A.f s ≫ A.act (β i)) (Limits.pullback.snd A.f s)
                (by rw [Category.assoc, A.act_over]; exact Limits.pullback.condition) ≫ ψ' = ψ' ≫ E.act (β i)) ∧
            (∀ hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
              Limits.pullback.lift ψ (Limits.pullback.snd E.f s) hψ ≫ ψ' = Limits.pullback.fst E.f s ≫ E.act ⟨_, hd⟩ ∧
              Limits.pullback.lift ψ' (Limits.pullback.snd A.f s) hψ' ≫ ψ = Limits.pullback.fst A.f s ≫ A.act ⟨_, hd⟩))),
          pt S' s φ hφ φ' hφ' h₁ h₂ h₃ = pt S' s ψ hψ ψ' hψ' k₁ k₂ k₃ → φ = ψ ∧ φ' = ψ') ∧
      IsSeparated πX ∧ LocallyOfFiniteType πX ∧ LocallyOfFinitePresentation πX := by sorry
