-- Prove2me | Theorems.Thm_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal
-- name    : AdicCompletion.exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/a8798e8a-394d-5310-b88b-99f4a4857e2d
-- title:
--   Adic completions of a module-finite algebra at a maximal ideal
-- statement:
--   Let $B$ be a Noetherian commutative ring, $C$ a commutative $B$-algebra which is finite as a $B$-module, and $\mathfrak n \subset C$ a maximal ideal; put $\mathfrak m := (\operatorname{algebraMap} B\,C)^{-1}(\mathfrak n)$, the contraction of $\mathfrak n$ to $B$. The assertion is the existence of an algebra structure on the $\mathfrak n$-adic completion $\operatorname{AdicCompletion} \mathfrak n\, C$ over the $\mathfrak m$-adic completion $\operatorname{AdicCompletion} \mathfrak m\, B$ (note that these are the adic completions with respect to these ideals, not localisations followed by completion), together with a scalar-tower structure making the composite $B \to \operatorname{AdicCompletion} \mathfrak m\, B \to \operatorname{AdicCompletion} \mathfrak n\, C$ agree with the given $B$-action on $\operatorname{AdicCompletion} \mathfrak n\, C$, such that two conditions hold: first, $\operatorname{AdicCompletion} \mathfrak n\, C$ is a finite module over $\operatorname{AdicCompletion} \mathfrak m\, B$; second, if moreover $C$ is flat as a $B$-module, then the structure ring map $\operatorname{AdicCompletion} \mathfrak m\, B \to \operatorname{AdicCompletion} \mathfrak n\, C$ is injective. The flatness assumption occurs only as the hypothesis of this second, conditional, clause.
--
--   This is the standard transfer of module-finiteness (and, under flatness, of injectivity of the structure map) from a finite algebra $B \to C$ to the completions at a maximal ideal of $C$ and its contraction to $B$. It is used in the analysis of the local structure of modular curves at a point, where a stalk of a torsion-lifting construction must be recognised as a finite algebra with injective structure map over the completion of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem AdicCompletion.exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal
    (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] [Algebra B C] [Module.Finite B C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] :
    ∃ (_ : Algebra (AdicCompletion (𝔫.comap (algebraMap B C)) B) (AdicCompletion 𝔫 C))
      (_ : IsScalarTower B (AdicCompletion (𝔫.comap (algebraMap B C)) B) (AdicCompletion 𝔫 C)),
      Module.Finite (AdicCompletion (𝔫.comap (algebraMap B C)) B) (AdicCompletion 𝔫 C) ∧
      (Module.Flat B C →
        Function.Injective (algebraMap (AdicCompletion (𝔫.comap (algebraMap B C)) B) (AdicCompletion 𝔫 C))) := by sorry
