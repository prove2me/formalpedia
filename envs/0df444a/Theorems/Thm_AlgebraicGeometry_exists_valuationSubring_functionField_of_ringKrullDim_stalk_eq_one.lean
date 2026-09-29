-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
-- name    : AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/48e7cf8c-cd99-50e5-8fd1-10fa8b535af1
-- title:
--   Restricting a codimension-one valuation along a dominant map
-- statement:
--   Let $k$ be a field and let $fX : X \to \operatorname{Spec} k$, $fY : Y \to \operatorname{Spec} k$ be morphisms of schemes, with $X$ integral, $fX$ locally of finite type and quasi-compact, $Y$ integral and $fY$ proper. Let $U$ be an open subscheme of $X$ and $\alpha : U \to Y$ a morphism over $k$ (i.e. $\alpha$ followed by $fY$ equals the inclusion $U \hookrightarrow X$ followed by $fX$) whose underlying map of spaces has dense image. Let $z \in U$ be a point such that $\mathcal{O}_{X,z}$ has Krull dimension $1$ and is integrally closed, and such that $\mathcal{O}_{Y,\alpha(z)}$ has Krull dimension $\neq 0$. Then there exist: a valuation subring $O \neq \top$ of the function field $k(Y)$; a morphism $\ell_0 : \operatorname{Spec} O \to Y$ with $\operatorname{Spec}$ of the inclusion $O \hookrightarrow k(Y)$ followed by $\ell_0$ equal to the canonical map $\operatorname{Spec} k(Y) \to Y$ at the generic point; a natural number $d$ with $d+1 = \dim Y$ as topological Krull dimension; elements $g_0,\dots,g_{d-1} \in O \subseteq k(Y)$ such that every $Q \in k[T_0,\dots,T_{d-1}]$ with $O.\mathrm{valuation}(Q(g)) < 1$ vanishes, where $k$ acts on $k(Y)$ through $fY$ and the germ at the generic point; and a ring homomorphism $\varphi : O \to \mathcal{O}_{X,z}$ which is local and satisfies $\operatorname{Spec}\varphi$ followed by $\ell_0$ equal to the canonical map $\operatorname{Spec}\mathcal{O}_{X,z} \to U$ followed by $\alpha$.
--
--   This is the valuation-restriction step in Rosenlicht's lemma on extending rational maps to proper targets: the discrete valuation of $k(X)$ attached to a normal codimension-one point $z$ is pulled back along $\alpha^{*} : k(Y) \hookrightarrow k(X)$ to a valuation subring of $k(Y)$ which is centred on $Y$ and whose residue field has transcendence degree at least $\dim Y - 1$ over $k$, recorded here through algebraically independent residues $g_i$. It feeds the construction of a proper model with a prescribed codimension-one local ring, via [`AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one`](thm.html#AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType fX] [QuasiCompact fX] [IsIntegral Y] [IsProper fY]
    (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (hα : α ≫ fY = U.ι ≫ fX) (hdom : DenseRange α.base)
    (z : X) (hzU : z ∈ U) (hz₁ : ringKrullDim (X.presheaf.stalk z) = 1)
    (hzn : IsIntegrallyClosed (X.presheaf.stalk z))
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) ≠ 0) :
    ∃ (O : ValuationSubring Y.functionField) (_ : O ≠ ⊤) (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap O Y.functionField)) ≫ ℓ₀ = Y.fromSpecStalk (genericPoint Y))
      (d : ℕ) (_ : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Y)
      (g : Fin d → Y.functionField) (_ : ∀ i, g i ∈ O)
      (_ : ∀ Q : MvPolynomial (Fin d) k,
        O.valuation (Q.eval₂ ((Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom.comp
          (fY.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) g) < 1 → Q = 0)
      (φ : CommRingCat.of O ⟶ X.presheaf.stalk z),
      IsLocalHom φ.hom ∧ Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α := by sorry
