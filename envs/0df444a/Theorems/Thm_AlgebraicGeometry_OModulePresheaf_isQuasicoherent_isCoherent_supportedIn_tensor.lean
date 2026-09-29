-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor
-- name    : AlgebraicGeometry.OModulePresheaf.isQuasicoherent_isCoherent_supportedIn_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/404313a7-704d-53f2-83be-2acf82912e4c
-- title:
--   Open-by-open tensor product preserves quasi-coherence, coherence, support
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a morphism, and let $F$, $G$ be two objects of `OModulePresheaf π`: each assigns to every open $U \subseteq V$ an abelian group $F(U)$ carrying compatible $R$- and $\Gamma(V,U)$-module structures (the $R$-action factoring through the algebra map $R \to \Gamma(V,U)$ induced by $\pi$), together with $R$-linear restrictions $F(U') \to F(U)$ for $U \le U'$ that are semilinear over restriction of functions and satisfy the identity and composition laws; no sheaf condition is imposed. Let $F \otimes G$ be the open-by-open tensor product `F.tensor G`, with $(F \otimes G)(U) = F(U) \otimes_{\Gamma(V,U)} G(U)$ and the induced restrictions. The theorem asserts the conjunction of three statements. First, if $F$ and $G$ are quasi-coherent in the elementwise sense — for every affine open $U$ and every $f \in \Gamma(V,U)$, every $x \in F(V.\mathrm{basicOpen}\, f)$ satisfies $F(U) \ni y \mapsto y|_{D(f)} = (f^n|_{D(f)}) \cdot x$ for some $n$ and some $y$, and every $y \in F(U)$ restricting to $0$ on $D(f)$ is annihilated by some $f^n$ — then so is $F \otimes G$. Second, if $F(U)$ and $G(U)$ are finite $\Gamma(V,U)$-modules for every affine open $U$, then so is $(F \otimes G)(U)$. Third, for every closed subset $Y \subseteq V$, if one of $F$, $G$ is supported in $Y$ in the sense that its sections over every affine open disjoint from $Y$ form a subsingleton, then the same holds for $F \otimes G$.
--
--   This packages the standard facts that localisation commutes with tensor products, that a tensor product of finitely generated modules is finitely generated, and that a tensor product with a trivial module is trivial, in the affine-local formulation used for presheaves of modules over a scheme. It is the bookkeeping step that allows a coherent, quasi-coherent datum supported in a closed subset to be twisted by an invertible sheaf, and is used in the computations of Euler characteristics of twisted tensor powers and in the deformation-theoretic applications that rely on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_isCoherent_supportedIn_tensor
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F G : OModulePresheaf π) :
    (F.IsQuasicoherent → G.IsQuasicoherent → (F.tensor G).IsQuasicoherent) ∧
    (F.IsCoherent → G.IsCoherent → (F.tensor G).IsCoherent) ∧
    (∀ Y : TopologicalSpace.Closeds V, F.SupportedIn Y ∨ G.SupportedIn Y → (F.tensor G).SupportedIn Y) := by sorry
