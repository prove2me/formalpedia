-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_apply_comp_eq_pullback_comp_of_apply_eq_pullback
-- name    : AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/4b10a75f-1c17-53bd-b5cc-4c117330f30a
-- title:
--   Composing section-ring comparison maps along d gg c
-- statement:
--   Let $c : X' \to X$ and $d : X'' \to X'$ be morphisms of schemes, let $L$, $L'$, $L''$ be modules on $X$, $X'$, $X''$ respectively, and let $e : c^{*}L \cong L'$ and $e' : d^{*}L' \cong L''$ be isomorphisms of modules. Let $S, S', S''$ be commutative rings, $R$ an $S$-algebra with a family of $S$-submodules $\mathcal R_n \subseteq R$ indexed by $n \in \mathbb N$, and similarly $(R', \mathcal R'_n)$ over $S'$ and $(R'', \mathcal R''_n)$ over $S''$; no grading axioms are imposed on these families. Let $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$, $\iota'_n$, $\iota''_n$ be maps into the global sections of the iterated tensor powers $L^{\otimes n}$, defined by $L^{\otimes 0} = \mathbf 1$ and $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$. Let $\vartheta : R \to R'$ and $\vartheta' : R' \to R''$ be ring homomorphisms with $\vartheta(\mathcal R_n) \subseteq \mathcal R'_n$ and $\vartheta'(\mathcal R'_n) \subseteq \mathcal R''_n$ for all $n$. Assume that for all $n$ and $x \in \mathcal R_n$ the section $\iota'_n(\vartheta x)$ is obtained from $\iota_n(x)$ by applying the unit of the pullback–pushforward adjunction for $c$ at $L^{\otimes n}$, evaluated on $\top$, followed by the global sections of the canonical isomorphism $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n}$ (built from the monoidal structure of $c^{*}$) composed with the $n$-th tensor power of $e$; and assume the analogous formula for $\vartheta'$ with $d$, $L'$ and $e'$. Then for all $n$ and $x \in \mathcal R_n$, $\iota''_n(\vartheta'(\vartheta x))$ is obtained from $\iota_n(x)$ by the same recipe for the composite $d \gg c$, read through the $n$-th tensor power of the identification $(d \gg c)^{*}L \cong d^{*}c^{*}L \cong d^{*}L' \cong L''$ coming from `Scheme.Modules.pullbackComp`, $d^{*}e$ and $e'$.
--
--   This is the transitivity (cocycle) statement for the comparison maps between graded rings of sections of tensor powers of a module: degreewise pullback along $c$ followed by degreewise pullback along $d$ is degreewise pullback along $d \gg c$, with the identifications of pullbacks of tensor powers composed accordingly. It is used in the construction of section rings of rigidified line bundles, where it feeds the cocycle compatibility statement [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_apply_comp_eq_pullback_comp_of_apply_eq_pullback.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

theorem AlgebraicGeometry.GradedOAlgebra.apply_comp_eq_pullback_comp_of_apply_eq_pullback
    {X X' X'' : Scheme.{u}} (c : X' ⟶ X) (d : X'' ⟶ X')
    (L : X.Modules) (L' : X'.Modules) (L'' : X''.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L') (e' : (Scheme.Modules.pullback d).obj L' ≅ L'')
    {S S' S'' : Type u} [CommRing S] [CommRing S'] [CommRing S'']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R)
    (R' : Type u) [CommRing R'] [Algebra S' R'] (𝓡' : ℕ → Submodule S' R')
    (R'' : Type u) [CommRing R''] [Algebra S'' R''] (𝓡'' : ℕ → Submodule S'' R'')
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤))
    (ι'' : ∀ n : ℕ, 𝓡'' n → Γ(L''.tensorPow n, ⊤))
    (ϑ : R →+* R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (ϑ' : R' →+* R'') (hϑ'deg : ∀ n, ∀ x ∈ 𝓡' n, ϑ' x ∈ 𝓡'' n)
    (hϑ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)))
    (hϑ' : ∀ (n : ℕ) (x : 𝓡' n), ι'' n ⟨ϑ' x, hϑ'deg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso d L' n ≪≫ Scheme.Modules.tensorPowMapIso e' n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction d).unit.app (L'.tensorPow n)).app ⊤) (ι' n x))) :
    ∀ (n : ℕ) (x : 𝓡 n), ι'' n ⟨ϑ' (ϑ x), hϑ'deg n _ (hϑdeg n x x.2)⟩ =
        ((Scheme.Modules.pullbackTensorPowIso (d ≫ c) L n ≪≫ Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackComp d c).app L).symm ≪≫ (Scheme.Modules.pullback d).mapIso e ≪≫ e') n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction (d ≫ c)).unit.app (L.tensorPow n)).app ⊤) (ι n x)) := by sorry
