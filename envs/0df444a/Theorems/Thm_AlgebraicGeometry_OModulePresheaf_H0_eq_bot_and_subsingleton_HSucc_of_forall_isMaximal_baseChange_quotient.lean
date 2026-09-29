-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
-- name    : AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/f231f0a3-872d-501c-992b-48685ab2c393
-- title:
--   Fibrewise acyclicity implies acyclicity over the base
-- statement:
--   Let $B$ be a commutative ring, $P$ a scheme and $\varpi\colon P \to \operatorname{Spec} B$ a separated morphism, and let $\mathfrak W$ be an ordered affine cover of $P$: a finite linearly ordered index type $\iota$ together with opens $U_i$ that are affine and satisfy $\bigsqcup_i U_i = \top$. Assume (hflat) that for every $i \in \mathbb N$ and every strictly monotone $s\colon \mathrm{Fin}(i+1) \to \iota$ the ring $\Gamma(P, \bigcap_j U_{s(j)})$ is flat as a $B$-module, for the $B$-algebra structure induced by $\varpi$. Let $N$ be an $\mathcal O_P$-module which is invertible in the sense that every point of $P$ has an open neighbourhood $U$ with $N|_U$ isomorphic to the unit sheaf of modules on $U$, and form the presheaf of $B$-modules $U \mapsto \Gamma(N, U)$ together with its alternating Čech complex on $\mathfrak W$. Assume (hfin) that this complex has finitely generated cohomology over $B$, i.e. $\ker d^0$ and each $\ker d^{i+1}/\operatorname{im} d^i$ are finite $B$-modules; and assume (hfib) that for every maximal ideal $\mathfrak m \subset B$ the corresponding data over $B/\mathfrak m$ — the second projection from $P \times_{\operatorname{Spec} B} \operatorname{Spec}(B/\mathfrak m)$, the pullback of $N$ along the first projection, and the cover $\mathfrak W$ pulled back along that first projection — has vanishing Čech cohomology, that is $\ker d^0 = \bot$ and each $\ker d^{i+1}/\operatorname{im} d^i$ is a subsingleton. The conclusion is the same vanishing over $B$ itself: $\ker d^0 = \bot$ for the Čech complex of $N$ on $\mathfrak W$, and $\ker d^{i+1}/\operatorname{im} d^i$ is a subsingleton for every $i$.
--
--   This is the cohomology-and-base-change form of Nakayama's argument: acyclicity of an invertible sheaf on all closed fibres of a separated morphism to an affine base propagates to acyclicity of the Čech complex over the base, under flatness of the chart intersections and finiteness of the Čech cohomology. It is used in the study of the relative Picard functor, namely in the construction of isomorphisms between tensor products and pullbacks of translated line bundles for a polarisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
    {B : Type u} [CommRing B] {P : Scheme.{u}} (ϖ : P ⟶ Spec (CommRingCat.of B)) [IsSeparated ϖ]
    (𝔚 : P.OrderedAffineCover)
    (hflat : ∀ (i : ℕ) (s : 𝔚.Idx i),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom ϖ (𝔚.inter s); Module.Flat B Γ(P, 𝔚.inter s))
    (N : P.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hfin : (OModulePresheaf.ofModules ϖ N).CechFinite 𝔚)
    (hfib : ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal),
      (OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))
          ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj N)).H0
          (𝔚.baseChange ϖ (B ⧸ 𝔪)) = ⊥ ∧
        ∀ i, Subsingleton
          ((OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))
            ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj N)).HSucc
            (𝔚.baseChange ϖ (B ⧸ 𝔪)) i)) :
    (OModulePresheaf.ofModules ϖ N).H0 𝔚 = ⊥ ∧ ∀ i, Subsingleton ((OModulePresheaf.ofModules ϖ N).HSucc 𝔚 i) := by sorry
