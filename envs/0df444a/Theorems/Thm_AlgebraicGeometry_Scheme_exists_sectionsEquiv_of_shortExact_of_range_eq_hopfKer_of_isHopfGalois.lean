-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois
-- name    : AlgebraicGeometry.Scheme.exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/eef81f6e-6968-578f-8e1c-cdbe3a982eb7
-- title:
--   Fppf quotient sheaf represented by the Hopf kernel
-- statement:
--   Let $S$ be a scheme, and let $S.\mathrm{Fppf}$ denote the category of schemes over $S$ whose structure morphism is flat and locally of finite presentation, equipped with the small fppf Grothendieck topology. Let $A$ be a commutative ring with a Hopf algebra structure over $\mathbb Z$ which is of finite type as a $\mathbb Z$-algebra, let $B$ be a commutative $\mathbb Z$-Hopf algebra, and let $qc : A \to B$ be a morphism of bialgebras. Let $K$ be a commutative $\mathbb Z$-Hopf algebra of finite type and $j : K \to A$ an injective morphism of bialgebras whose underlying algebra map has image exactly $\mathrm{hopfKer}\,qc$, the equaliser of $a \mapsto (\mathrm{id}_A \otimes qc)(\Delta a)$ and $a \mapsto a \otimes 1$ inside $A \otimes_{\mathbb Z} B$. Assume $qc$ is Hopf–Galois, i.e. the canonical $\mathbb Z$-linear map $A \otimes_{\mathbb Z} A \to A \otimes_{\mathbb Z} B$ is surjective and every element of its kernel lies in the span of the balancing relations $(ah) \otimes a' - a \otimes (ha')$ with $h \in \mathrm{hopfKer}\,qc$; and assume $A$ is faithfully flat as a module over $\mathrm{hopfKer}\,qc$. Let $F_0 \xrightarrow{\iota} F_1 \xrightarrow{\mathrm{pr}} L$ be morphisms of sheaves of abelian groups on this site with $\iota$ followed by $\mathrm{pr}$ zero and the resulting short complex short exact. Suppose given, for each object $U$, additive isomorphisms $e_1(U) : F_1(U) \cong \mathrm{Hom}_{\mathbb Z\text{-alg}}(A, \Gamma(U,\mathcal O))$ and $e_0(U) : F_0(U) \cong \mathrm{Hom}_{\mathbb Z\text{-alg}}(B, \Gamma(U,\mathcal O))$, the right-hand sides being groups under convolution written additively, such that $e_1$ is natural (for $f : U \to V$, $s \in F_1(V)$ and $a \in A$, $e_1(U)(F_1(f)s)(a)$ is the image of $e_1(V)(s)(a)$ under the pullback on global sections) and such that $e_1(U)(\iota(s))(a) = e_0(U)(s)(qc\,a)$ for all $s \in F_0(U)$, $a \in A$. Then there exists a family of additive isomorphisms $e(U) : L(U) \cong \mathrm{Hom}_{\mathbb Z\text{-alg}}(K, \Gamma(U,\mathcal O))$, again with convolution as group law, which is compatible with $\mathrm{pr}$, in the sense that $e(U)(\mathrm{pr}(s))(k) = e_1(U)(s)(j\,k)$ for all $s \in F_1(U)$ and $k \in K$, and natural in $U$, in the sense that $e(U)(L(f)s)(k)$ is the image of $e(V)(s)(k)$ under the pullback on global sections for every $f : U \to V$, $s \in L(V)$ and $k \in K$.
--
--   This is the affine, Hopf-algebraic form of the statement that for a closed subgroup scheme $H \subseteq G$ of affine commutative group schemes with $G$ faithfully flat over $G/H$, the fppf quotient sheaf is represented by $\mathrm{Spec}$ of the Hopf kernel: given a short exact sequence of fppf sheaves whose first two terms are the points functors of $\mathrm{Spec}\,B \subseteq \mathrm{Spec}\,A$, the quotient sheaf is identified with the points functor of $\mathrm{Spec}\,K$. It is used in the study of the Néron model of $J_0$ and its primary torsion, via [`ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

theorem AlgebraicGeometry.Scheme.exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois
    (S : Scheme.{0})
    (A : Type) [CommRing A] [HopfAlgebra ℤ A] [Algebra.FiniteType ℤ A]
    (B : Type) [CommRing B] [HopfAlgebra ℤ B] (qc : A →ₐc[ℤ] B)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K]
    (j : K →ₐc[ℤ] A) (hinj : Function.Injective j)
    (hrange : (j : K →ₐ[ℤ] A).range = HopfAlgebra.hopfKer qc)
    (hHG : HopfAlgebra.IsHopfGalois qc)
    (hff : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) A)
    (F₀ F₁ L : Sheaf (smallFppfTopology S) Ab.{1})
    (incl : F₀ ⟶ F₁) (pr : F₁ ⟶ L) (hzero : incl ≫ pr = 0)
    (hses : (ShortComplex.mk incl pr hzero).ShortExact)
    (e₁ : ∀ U : S.Fppf, F₁.1.obj (op U) ≃+ Additive (WithConv (A →ₐ[ℤ] Γ(U.left, ⊤))))
    (he₁ : ∀ {U V : S.Fppf} (f : U ⟶ V) (s : F₁.1.obj (op V)) (a : A),
      (Additive.toMul (e₁ U (F₁.1.map f.op s))) a
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e₁ V s)) a))
    (e₀ : ∀ U : S.Fppf, F₀.1.obj (op U) ≃+ Additive (WithConv (B →ₐ[ℤ] Γ(U.left, ⊤))))
    (hincl : ∀ (U : S.Fppf) (s : F₀.1.obj (op U)) (a : A),
      (Additive.toMul (e₁ U (incl.1.app (op U) s))) a = (Additive.toMul (e₀ U s)) (qc a)) :
    ∃ e : ∀ U : S.Fppf, L.1.obj (op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))),
      (∀ (U : S.Fppf) (s : F₁.1.obj (op U)) (k : K),
        (Additive.toMul (e U (pr.1.app (op U) s))) k = (Additive.toMul (e₁ U s)) (j k)) ∧
      ∀ {U V : S.Fppf} (f : U ⟶ V) (s : L.1.obj (op V)) (k : K),
        (Additive.toMul (e U (L.1.map f.op s))) k
          = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k) := by sorry
