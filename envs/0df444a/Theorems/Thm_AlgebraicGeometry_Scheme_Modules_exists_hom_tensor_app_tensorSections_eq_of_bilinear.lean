-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear
-- name    : AlgebraicGeometry.Scheme.Modules.exists_hom_tensor_app_tensorSections_eq_of_bilinear
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/67c76e95-9bf9-58a8-b9f7-fd4f3bc133a6
-- title:
--   Descent of a natural bilinear pairing to L ⊗ M → P
-- statement:
--   Let $X$ be a scheme and let $L$, $M$, $P$ be sheaves of $\mathcal O_X$-modules, i.e. objects of `X.Modules`. Suppose given, for every open $U \subseteq X$, a map $B_U \colon \Gamma(L,U) \to \Gamma(M,U) \to \Gamma(P,U)$ that is $\Gamma(X,U)$-linear in each argument (an iterated linear map over the ring of sections of $\mathcal O_X$ on $U$), and suppose these pairings are compatible with restriction: for every inclusion $i \colon V \to U$ of opens of $X$ and all $s \in \Gamma(L,U)$, $t \in \Gamma(M,U)$, the restriction along $i$ of $B_U(s,t)$ equals $B_V(s|_V, t|_V)$, the restrictions being those of the presheaves underlying $L$, $M$, $P$. The conclusion is that there exists a morphism $\nu \colon L \otimes M \to P$ of sheaves of $\mathcal O_X$-modules, for the monoidal structure on `X.Modules`, such that for every open $U$ and all sections $s \in \Gamma(L,U)$, $t \in \Gamma(M,U)$ the component of $\nu$ over $U$ sends `Scheme.Modules.tensorSections s t` to $B_U(s,t)$; here `tensorSections s t` is the section of $L \otimes M$ over $U$ obtained from the elementary tensor $s \otimes_{\Gamma(X,U)} t$ in the sectionwise tensor product by the map `tensorSectionsHom`, namely the unit of the sheafification adjunction for sheaves of modules followed by the comparison isomorphism `tensorIsoSheafify` identifying the sheafified presheaf tensor product with $L \otimes M$. Only existence is asserted, not uniqueness.
--
--   This is the universal property of the tensor product of sheaves of modules in the form actually needed when a pairing is constructed open by open: a pairing of sections, natural in the open set, factors through $L \otimes_{\mathcal O_X} M$ with the expected value on elementary tensors. It is used in the construction of isomorphisms out of tensor products of sheaves attached to eigen-subdata in the treatment of the relative group law on Jacobians of good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensor_app_tensorSections_eq_of_bilinear.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_tensor_app_tensorSections_eq_of_bilinear
    {X : Scheme.{u}} (L M P : X.Modules)
    (B : ∀ U : X.Opens, Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(P, U))
    (hB : ∀ {U V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (t : Γ(M, U)),
      P.presheaf.map i.op (B U s t) = B V (L.presheaf.map i.op s) (M.presheaf.map i.op t)) :
    ∃ ν : L ⊗ M ⟶ P, ∀ (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)),
      ν.app U (Scheme.Modules.tensorSections s t) = B U s t := by sorry
