-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra
-- name    : AlgebraicGeometry.exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/8f945263-26c4-5035-b127-596483c9f423
-- title:
--   Hull embedding into the Kummer sheaf μ_q over Specℤ
-- statement:
--   Fix natural numbers $p$ and $q$ with $q \neq 0$, a commutative ring $K$ carrying a Hopf algebra structure over $\mathbf Z$, and a homomorphism of $\mathbf Z$-bialgebras $\iota \colon \mathbf Z[\mathbf Z/q] \to K$, where $\mathbf Z[\mathbf Z/q]$ is the monoid algebra on $\mathrm{Multiplicative}(\mathbf Z/q)$. Assume that for every commutative ring $R$: composition with $\iota$ is injective on $\mathbf Z$-algebra maps $K \to R$, and a $\mathbf Z$-algebra map $g \colon \mathbf Z[\mathbf Z/q] \to R$ factors through $\iota$ exactly when there is $a \in R$ with $a - 1 \in (p)$ and $a\,(g(h) - \varepsilon(h)) = 0$ for all $h$, $\varepsilon$ the counit of $\mathbf Z[\mathbf Z/q]$. Let $L$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}\mathbf Z$ (objects: $\operatorname{Spec}\mathbf Z$-schemes flat and locally of finite presentation), together with isomorphisms $e_U \colon L(U) \cong \operatorname{Hom}_{\mathbf Z\text{-alg}}(K, \Gamma(U,\mathcal O))$, the latter with its convolution group law written additively, natural in the sense that $e_U(s|_U)(k) = \Gamma(f)(e_V(s)(k))$ for $f \colon U \to V$, $s \in L(V)$, $k \in K$. Let $C$ be a sheaf of abelian groups whose underlying presheaf is isomorphic, via $i_C$, to the restriction of the universe-lifted kernel of the $q$-th power map on the multiplicative-group sheaf, i.e. of $\mu_q$. Then there exists a morphism of sheaves $f \colon L \to C$ such that $f_U$ is injective on sections for every $U$, and for every $U$ and every $s \in C(U)$, $s$ lies in the image of $f_U$ if and only if there is $a \in \Gamma(U,\mathcal O)$ with $a - 1 \in (p)$ and $a\,(u_s - 1) = 0$, where $u_s \in \Gamma(U,\mathcal O)^\times$ is the unit obtained from $i_C(s)$ by the inclusion $\mu_q \hookrightarrow \mathbf G_m$.
--
--   This is the transport statement for Mazur's subgroup functor $\mu_q^\flat \subseteq \mu_q$ of points that are trivial in a neighbourhood of the fibre at $p$: an abelian fppf sheaf on $\operatorname{Spec}\mathbf Z$ whose sections are the $\mathbf Z$-algebra points of the Hopf algebra $K$ under convolution is identified with the subsheaf of $\mu_q$ cut out by the stated congruence condition. It serves the multiplicative branch of the dichotomy for the group schemes arising in the Kummer-type exact sequences, and is used by [`AlgebraicGeometry.nonempty_iso_or_natCard_algHom_eq_one_and_exists_shortExact_of_sectionsEquiv_convPow_of_ne_two`](thm.html#AlgebraicGeometry.nonempty_iso_or_natCard_algHom_eq_one_and_exists_shortExact_of_sectionsEquiv_convPow_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem AlgebraicGeometry.exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra
    (p q : ℕ) [NeZero q]
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K)
    (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐc[ℤ] K)
    (hι : ∀ (R : Type) [CommRing R],
        (∀ f g : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) =
            g.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) → f = g) ∧
        ∀ g : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] R,
          (∃ f : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) = g) ↔
            ∃ a : R, a - 1 ∈ Ideal.span {(p : R)} ∧
              ∀ h : MonoidAlgebra ℤ (Multiplicative (ZMod q)),
                a * (g h - algebraMap ℤ R
                  (Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q))) h)) = 0)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj) :
    ∃ f : L ⟶ C,
      (∀ U : specInt.Fppf, Function.Injective (f.hom.app (Opposite.op U))) ∧
      ∀ (U : specInt.Fppf) (s : C.obj.obj (Opposite.op U)),
        s ∈ Set.range (f.hom.app (Opposite.op U)) ↔
          ∃ a : Γ(U.left, ⊤), a - 1 ∈ Ideal.span {(p : Γ(U.left, ⊤))} ∧
            a * ((FppfKummerSES.gmLiftedSectionUnit
                    ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} q)).hom.app (Opposite.op U.left)
                      (iC.hom.app (Opposite.op U) s)) : Γ(U.left, ⊤)) - 1) = 0 := by sorry
