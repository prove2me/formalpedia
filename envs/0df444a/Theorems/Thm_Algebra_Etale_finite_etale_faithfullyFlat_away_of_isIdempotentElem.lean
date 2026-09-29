-- Prove2me | Theorems.Thm_Algebra_Etale_finite_etale_faithfullyFlat_away_of_isIdempotentElem
-- name    : Algebra.Etale.finite_etale_faithfullyFlat_away_of_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/6dc81c0f-eba7-5ef3-a76d-d5902b22c715
-- title:
--   Inverting an idempotent of a finite étale algebra
-- statement:
--   Let $S$ and $C$ be commutative rings with $C$ an $S$-algebra that is finite as an $S$-module and étale over $S$, and let $e \in C$ be an idempotent, $e^2 = e$. Assume that every prime $\mathfrak q$ of $S$ is the contraction along $S \to C$ of some prime $\mathfrak p$ of $C$ with $e \notin \mathfrak p$, i.e. that $\operatorname{Spec}$ of the localisation of $C$ away from $e$ surjects onto $\operatorname{Spec} S$. The conclusion is a conjunction of three assertions about the localisation $C[1/e]$, realised as `Localization.Away e`, viewed as an $S$-algebra through $S \to C \to C[1/e]$: it is finite as an $S$-module, it is étale over $S$, and it is faithfully flat as an $S$-module. No hypothesis is placed on $1 - e$, and no product decomposition of $C$ is asserted.
--
--   This is the standard statement that inverting an idempotent in a finite étale algebra again gives a finite étale algebra, faithfully flat as soon as the corresponding open-and-closed piece meets every fibre over $\operatorname{Spec} S$. It is used to produce a finite étale faithfully flat base change over which a basis adapted to a group law on a Jacobian can be chosen.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_finite_etale_faithfullyFlat_away_of_isIdempotentElem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.finite_etale_faithfullyFlat_away_of_isIdempotentElem
    {S C : Type} [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] [Algebra.Etale S C]
    (e : C) (he : IsIdempotentElem e)
    (hsurj : ∀ 𝔮 : Ideal S, 𝔮.IsPrime → ∃ 𝔭 : Ideal C, 𝔭.IsPrime ∧ 𝔭.comap (algebraMap S C) = 𝔮 ∧ e ∉ 𝔭) :
    Module.Finite S (Localization.Away e) ∧ Algebra.Etale S (Localization.Away e) ∧
      Module.FaithfullyFlat S (Localization.Away e) := by sorry
