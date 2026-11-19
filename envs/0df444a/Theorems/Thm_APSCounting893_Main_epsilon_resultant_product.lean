-- Prove2me | Theorems.Thm_APSCounting893_Main_epsilon_resultant_product
-- name    : APSCounting893.Main.epsilon_resultant_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:33:59.64263+00:00
-- url     : https://prove2.me/theorems/b7fe734b-6794-4376-b192-55c82e8f01c2
-- title:
--   Resultant product over the actual finite epsilon-limit set
-- statement:
--   Let $F$, the admissible line data, the separating form $\ell$, and the positive homogenizing degrees be as in Lemma 5.2. Let $S$ be a finite enumeration of the actual projective epsilon-limit set $Z_0^*$.
--
--   There are positive integer multiplicities $\mu_z$ and nonzero scalar rescalings $\widetilde z$ of each projective representative $z\in S$ such that
--
--   $$\operatorname{TC}_{\epsilon}R(T,t,w,\epsilon)=\prod_{z\in S}H_{T,w}(\widetilde z)^{\mu_z}.$$
--
--   Here $R$ is the actual normalized universal resultant of the perturbed equations and the prescribed quadratic form. The product includes limits at infinity, and every multiplicity is positive. This is the factorization assertion of Lemma 5.2 after its finite limit set has been enumerated.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 5.1, pp. 20–21, Lemma 5.2 and Remark 5.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf. Andrews, Garg and Schost, Hilbert’s Nullstellensatz is in the Counting Hierarchy, arXiv:2602.17904, https://arxiv.org/pdf/2602.17904, Lemma 4.7 (Ierardi Lemma 2.6), p. 26.

import Definitions.Def_APSCounting893_Main_Resultant
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.epsilon_resultant_product
    (F : ReducedMap) (D : LineData F) (lambda : Affine ℂ (F.n+1))
    (hsep : Set.InjOn (separatingForm lambda) (zeroFiber F D.c ∪ {0}))
    (degrees : Fin (F.n+(F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees)
    (S : Finset (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient))
    (hS : (S : Set _) = epsilonLimitSet F D.c D.alpha degrees) :
    ∃ (mu : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → ℕ)
      (representatives : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) →
        (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient)),
      (∀ z ∈ S, 0 < mu z ∧ ∃ a : PuiseuxAmbient, a ≠ 0 ∧ representatives z = a • z) ∧
      trailingEpsilonResultant (resultantFor F D.c D.alpha lambda degrees) =
        ∏ z ∈ S, HAtPoint F lambda (representatives z) ^ mu z := by sorry
