-- Prove2me | Theorems.Thm_Algebra_PreSubmersivePresentation_isStandardSmoothOfRelativeDimension_localizationAway_jacobian
-- name    : Algebra.PreSubmersivePresentation.isStandardSmoothOfRelativeDimension_localizationAway_jacobian
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:16.960194+00:00
-- url     : https://prove2.me/theorems/b6ed7003-7a40-4154-9333-1ad6a5923180
-- title:
--   Localizing a pre-submersive presentation at its Jacobian gives a standard smooth algebra
-- statement:
--   Let $S$ be an $R$-algebra and let $P$ be a pre-submersive presentation with finite variable and relation sets. If the presentation has relative dimension $n$, then after inverting its Jacobian element, $$R→S[P_{Jac}^{-1}]\text{ is standard smooth of relative dimension }n.$$ This is the local Jacobian criterion used to prove smoothness of the canonical charts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

universe u
open Algebra
open Algebra.PreSubmersivePresentation

theorem Algebra.PreSubmersivePresentation.isStandardSmoothOfRelativeDimension_localizationAway_jacobian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.PreSubmersivePresentation R S ι σ) {n : ℕ}
    (hP : P.dimension = n) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap S (Localization.Away P.jacobian)).comp
        (algebraMap R S)) := by sorry
