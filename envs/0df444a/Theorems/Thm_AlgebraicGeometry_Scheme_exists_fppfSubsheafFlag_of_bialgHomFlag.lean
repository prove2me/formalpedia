-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag
-- name    : AlgebraicGeometry.Scheme.exists_fppfSubsheafFlag_of_bialgHomFlag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/30947dd2-3cc1-5554-846c-c4ea24b89e13
-- title:
--   Flag of Hopf quotients yields flag of fppf subsheaves
-- statement:
--   Let $S$ be a scheme and let $\mathcal J$ be an abelian sheaf on the small fppf site of $S$, whose objects are the $S$-schemes $U \to S$ that are flat and locally of finite presentation (the small Grothendieck topology attached to the morphism property $\mathtt{Flat} \sqcap \mathtt{LocallyOfFinitePresentation}$). Let $H$ be a commutative ring carrying a Hopf $\mathbb Z$-algebra structure, and suppose given, for every object $U$ of the site, an isomorphism of additive groups $\mathcal J(U) \cong \operatorname{Hom}_{\mathbb Z\text{-alg}}(H, \Gamma(U,\mathcal O_U))$, the right-hand side being the convolution group written additively; suppose this family is natural, in the sense that for $f : U \to V$ in the site, $s \in \mathcal J(V)$ and $h \in H$, the algebra map attached to $f^{*}s$ sends $h$ to the image of the value at $h$ of the algebra map attached to $s$ under $\Gamma(f)$. Let $n \in \mathbb N$, let $B_0,\dots,B_n$ be commutative rings with Hopf $\mathbb Z$-algebra structures, let $\pi_i : H \to B_i$ be surjective bialgebra maps, and let $\varphi_i : B_{i+1} \to B_i$ be bialgebra maps with $\varphi_i \circ \pi_{i+1} = \pi_i$ for $i < n$, with $\pi_n$ bijective. The conclusion asserts the existence of abelian sheaves $F_0,\dots,F_n$ on the same site, morphisms $\iota_i : F_i \to \mathcal J$, morphisms $\mathrm{incl}_i : F_i \to F_{i+1}$ for $i < n$, and additive isomorphisms $F_i(U) \cong \operatorname{Hom}_{\mathbb Z\text{-alg}}(B_i, \Gamma(U,\mathcal O_U))$ (again convolution, written additively), such that every $\iota_i$ is a monomorphism, $\mathrm{incl}_i$ followed by $\iota_{i+1}$ equals $\iota_i$, $\iota_n$ is an isomorphism, and for all $i$, all $U$, all $s \in F_i(U)$ and all $h \in H$ the algebra map attached to $\iota_i(s)$ takes the value at $h$ of the algebra map attached to $s$ composed with $\pi_i$, i.e. $\iota_i$ corresponds to precomposition with $\pi_i$.
--
--   This records, purely in terms of functors of points on the fppf site, that a chain of Hopf-algebra quotients $H \twoheadrightarrow B_n \twoheadrightarrow \cdots \twoheadrightarrow B_0$ of a Hopf algebra representing $\mathcal J$ cuts out a flag of fppf subsheaves of $\mathcal J$, the subsheaf $F_i$ consisting of those sections whose associated ring map kills $\ker \pi_i$. It is used by [`ModularCurve.nonempty_jZeroNeronPrimaryTorsionFlag`](thm.html#ModularCurve.nonempty_jZeroNeronPrimaryTorsionFlag) to produce a filtration of the primary torsion of a Néron model by fppf subsheaves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

theorem AlgebraicGeometry.Scheme.exists_fppfSubsheafFlag_of_bialgHomFlag
    (S : Scheme.{0}) (𝒥 : Sheaf (smallFppfTopology S) Ab.{1})
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (sectionsEquiv : ∀ U : S.Fppf,
      𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (sectionsNat : ∀ {U V : S.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
      (Additive.toMul (sectionsEquiv U (𝒥.1.map f.op s))) h
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (sectionsEquiv V s)) h))
    (n : ℕ) (B : Fin (n + 1) → Type) [∀ i, CommRing (B i)] [∀ i, HopfAlgebra ℤ (B i)]
    (π : ∀ i, H →ₐc[ℤ] B i) (hπ : ∀ i, Function.Surjective (π i))
    (φ : ∀ i : Fin n, B i.succ →ₐc[ℤ] B i.castSucc)
    (hφ : ∀ i : Fin n, (φ i).comp (π i.succ) = π i.castSucc)
    (hlast : Function.Bijective (π (Fin.last n))) :
    ∃ (F : Fin (n + 1) → Sheaf (smallFppfTopology S) Ab.{1})
      (ι : ∀ i, F i ⟶ 𝒥) (incl : ∀ i : Fin n, F i.castSucc ⟶ F i.succ)
      (FE : ∀ (i : Fin (n + 1)) (U : S.Fppf),
        (F i).1.obj (op U) ≃+ Additive (WithConv (B i →ₐ[ℤ] Γ(U.left, ⊤)))),
      (∀ i, Mono (ι i)) ∧ (∀ i : Fin n, incl i ≫ ι i.succ = ι i.castSucc) ∧
      IsIso (ι (Fin.last n)) ∧
      ∀ (i : Fin (n + 1)) (U : S.Fppf) (s : (F i).1.obj (op U)) (h : H),
        WithConv.ofConv (Additive.toMul (sectionsEquiv U ((ι i).1.app (op U) s))) h
          = WithConv.ofConv (Additive.toMul (FE i U s)) (π i h) := by sorry
