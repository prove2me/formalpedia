-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial
-- name    : AlgebraicGeometry.OModulePresheaf.exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/c8d978cb-fb90-53cd-8419-ba4dc80ae4dd
-- title:
--   Base-change-compatible projective complex computing Čech cohomology of a locally trivial module
-- statement:
--   Let $R$ be a Noetherian commutative ring, $X$ a scheme and $\pi : X \to \operatorname{Spec} R$ a proper flat morphism, and let $M$ be a module over the structure sheaf of $X$ which is locally trivial in the sense that every point of $X$ lies in an open $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $\mathcal U$ be an ordered affine cover of $X$, i.e. a finite linearly ordered index set $\iota$ together with affine opens $U_i$ whose supremum is $X$, and let $n$ be a natural number with $\#\iota \le n+1$. Then there exist $R$-modules $K^i$ ($i \in \mathbb N$) that are finitely generated and projective, $R$-linear maps $\delta^i : K^i \to K^{i+1}$ with $\delta^{i+1} \circ \delta^i = 0$ and $K^i$ trivial for $i > n$, and $R$-linear maps $\varphi^i$ from $K^i$ to the $i$-th alternating Čech cochain module of $M$ on $\mathcal U$ — that is, the module of families indexed by the strictly monotone maps $s : \mathrm{Fin}(i+1) \to \iota$ of sections of $M$ over $\bigsqcap_j U_{s(j)}$, viewed as an $R$-module through $\pi$ — satisfying $d^i \circ \varphi^i = \varphi^{i+1} \circ \delta^i$; and moreover, for every commutative $R$-algebra $A$ and every $i$, an $A$-linear map $\Theta_A^i : A \otimes_R K^i \to \check C^i(\mathcal U_A, M_A)$, where $M_A$ is the pullback of $M$ along the first projection of $X \times_{\operatorname{Spec} R} \operatorname{Spec} A$, this fibre product is regarded over $\operatorname{Spec} A$ by the second projection, and $\mathcal U_A$ is the cover by the preimages of the $U_i$ under the first projection, such that for every such $A$: (a) the $\Theta_A^i$ commute with the differentials, $\Theta_A^{i+1} \circ (\delta^i \otimes A) = d^i \circ \Theta_A^i$; (b) on pure tensors, $\Theta_A^i(a \otimes k)$ has $s$-component $a$ times the restriction to the corresponding intersection in $\mathcal U_A$ of the image of $\varphi^i(k)_s$ under the unit of the pullback–pushforward adjunction for the first projection; (c) an element $x$ of $A \otimes_R K^0$ killed by $\delta^0 \otimes A$ and by $\Theta_A^0$ is zero; (d) every $y$ with $d^0 y = 0$ equals $\Theta_A^0 x$ for some $x$ with $(\delta^0 \otimes A)(x) = 0$; (e) for each $i$, an $x$ in $A \otimes_R K^{i+1}$ with $(\delta^{i+1} \otimes A)(x) = 0$ whose image $\Theta_A^{i+1}(x)$ lies in the range of $d^i$ lies in the range of $\delta^i \otimes A$; and (f) for each $i$, every $y$ in $\check C^{i+1}(\mathcal U_A, M_A)$ with $d^{i+1} y = 0$ satisfies $\Theta_A^{i+1}(x) - y \in \operatorname{range} d^i$ for some $x$ with $(\delta^{i+1} \otimes A)(x) = 0$. Clauses (c)–(f) are the elementwise form of the assertion that $\Theta_A$ is a quasi-isomorphism from $A \otimes_R K^\bullet$ to the Čech complex of $M_A$ on $\mathcal U_A$.
--
--   This is the cohomology-and-base-change statement for a proper flat family and a locally trivial sheaf, in the form of a single bounded complex of finitely generated projective $R$-modules computing the Čech cohomology of the sheaf after every base change (Mumford's lemma on cohomology and base change; compare Hartshorne III.12). It is used in the construction of the polarisation data, where it is specialised to stalks of the base and to comap covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    [IsProper π] [Flat π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) (n : ℕ) (hn : Fintype.card 𝒰.ι ≤ n + 1) :
    ∃ (K : ℕ → Type u) (_ : ∀ i, AddCommGroup (K i)) (_ : ∀ i, Module R (K i))
      (_ : ∀ i, Module.Finite R (K i)) (_ : ∀ i, Module.Projective R (K i))
      (δ : ∀ i, K i →ₗ[R] K (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, n < i → Subsingleton (K i))
      (φ : ∀ i, K i →ₗ[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i)
      (_ : ∀ i, (OModulePresheaf.ofModules π M).d 𝒰 i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
      (Θ : ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ), A ⊗[R] K i →ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) i),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        (∀ i : ℕ, Θ A (i + 1) ∘ₗ (δ i).baseChange A
          = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i
            ∘ₗ Θ A i) ∧
        (∀ (i : ℕ) (a : A) (k : K i) (s : 𝒰.Idx i),
          Θ A i (a ⊗ₜ[R] k) s
            = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).res
                (𝒰.baseChange_inter_le π A s)
                ((((Scheme.Modules.pullbackPushforwardAdjunction
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app
                  (𝒰.inter s)).hom (φ i k s))) ∧
        (∀ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 → Θ A 0 x = 0 → x = 0) ∧
        (∀ y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) 0,
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) 0 y = 0 →
          ∃ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 ∧ Θ A 0 x = y) ∧
        (∀ (i : ℕ) (x : A ⊗[R] K (i + 1)), (δ (i + 1)).baseChange A x = 0 →
          Θ A (i + 1) x ∈ LinearMap.range
            ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i) →
          x ∈ LinearMap.range ((δ i).baseChange A)) ∧
        (∀ (i : ℕ) (y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) (i + 1)),
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) (i + 1) y = 0 →
          ∃ x : A ⊗[R] K (i + 1), (δ (i + 1)).baseChange A x = 0 ∧
            Θ A (i + 1) x - y ∈ LinearMap.range
              ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i)) := by sorry
