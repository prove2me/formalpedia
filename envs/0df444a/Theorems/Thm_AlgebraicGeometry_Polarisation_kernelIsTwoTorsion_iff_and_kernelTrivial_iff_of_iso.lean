-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_iff_and_kernelTrivial_iff_of_iso
-- name    : AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_iff_and_kernelTrivial_iff_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/ba6e3158-cc00-50c8-8b06-d42f1c2c1008
-- title:
--   Invariance of the two kernel conditions under isomorphism of modules
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme, $f \colon A \to \operatorname{Spec} R$ a morphism, and $L$ a `RelativeGroupLaw` for $f$, i.e. a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws, and naturality of multiplication under base change) on the sets $\mathrm{SchemeHomOver}\, t\, f = \{\varphi : T \to A \mid \varphi \circ f = t\}$ of $f$-sections over morphisms $t \colon T \to \operatorname{Spec} R$. Let $\mathcal{N}, \mathcal{N}'$ be modules on $A$ and $e \colon \mathcal{N} \cong \mathcal{N}'$ an isomorphism. The conclusion is the conjunction of two equivalences: $\mathrm{KernelIsTwoTorsion}\, f\, L\, \mathcal{N} \leftrightarrow \mathrm{KernelIsTwoTorsion}\, f\, L\, \mathcal{N}'$, and $\mathrm{KernelTrivial}\, f\, L\, \mathcal{N} \leftrightarrow \mathrm{KernelTrivial}\, f\, L\, \mathcal{N}'$. Here both predicates are stated in functor-of-points form: for every commutative ring $R'$, every $t \colon \operatorname{Spec} R' \to \operatorname{Spec} R$ and every $x \in \mathrm{SchemeHomOver}\, t\, f$, write $\Lambda(\mathcal{N}) = \mathrm{addMor}(f,L)^*\mathcal{N} \otimes (p_1^*\mathcal{N}^\vee \otimes p_2^*\mathcal{N}^\vee)$ on $A \times_{\operatorname{Spec} R} A$ and let $\mathrm{sliceAt}\, f\, x \colon \operatorname{pullback} f\, t \to \operatorname{pullback} f\, f$ be the morphism with components $p_1$ and $p_2$ followed by $x$; the slice condition asserts that $(\mathrm{sliceAt}\, f\, x)^*\Lambda(\mathcal{N})$ is isomorphic to the monoidal unit locally on the base, i.e. every point $s$ of $\operatorname{Spec} R'$ has an open neighbourhood $U$ such that the two modules become isomorphic after pullback along the inclusion of $(\mathrm{pullback.snd}\, f\, t)^{-1}U$. $\mathrm{KernelIsTwoTorsion}$ says this slice condition holds if and only if $L.\mathrm{mul}\, t\, x\, x = L.\mathrm{one}\, t$; $\mathrm{KernelTrivial}$ says it implies $x = L.\mathrm{one}\, t$.
--
--   The two predicates express, in the language of points, that the kernel $K(\mathcal{N})$ of the Mumford bundle attached to a module equals the $2$-torsion subgroup, respectively the unit section; the theorem records that both conditions depend only on the isomorphism class of the module. It is used when kernel conditions have to be transported across comparison isomorphisms (chosen representatives of isomorphism classes, base-change and composition isomorphisms), for instance in the results on existence of kernel-trivial modules over a discrete valuation ring and in the passage from trivial kernel to two-torsion kernel over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_iff_and_kernelTrivial_iff_of_iso.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_iff_and_kernelTrivial_iff_of_iso
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (𝓝 𝓝' : A.Modules) (e : 𝓝 ≅ 𝓝') :
    (KernelIsTwoTorsion f L 𝓝 ↔ KernelIsTwoTorsion f L 𝓝') ∧ (KernelTrivial f L 𝓝 ↔ KernelTrivial f L 𝓝') := by sorry
