-- Prove2me | Theorems.Thm_APSCounting893_Main_ierardi_resultant_factorization
-- name    : APSCounting893.Main.ierardi_resultant_factorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:25:35.597603+00:00
-- url     : https://prove2.me/theorems/f53dabc7-07d2-4b1d-988b-68646824233e
-- title:
--   Lemma 5.2 — Ierardi resultant factorization
-- statement:
--   For the actual homogenized and perturbed system, choose the source linear form $\ell$ injective on $Y_0\cup\{0\}$. Let $R$ be its normalized homogeneous resultant with $H_{T,w}$, and let $Z_0^*$ be the projective set of actual $\epsilon$-limits. This set is finite. There are positive integer multiplicities $\mu_z$ and compatible homogeneous representatives for which
--
--   $$\mathrm{TC}_{\epsilon}R=\prod_{z\in Z_0^*}H_{T,w}(z)^{\mu_z},\qquad\mu_z>0.$$
--
--   Points at infinity are retained. The representatives and nonzero rescalings are conclusions, so the literal product identity is not inserted into a definition or assumed as data. The identity is read after mapping the line parameter into the series field.
--
--   Differences from the source:
--   - reading: projective points z in the homogeneous evaluations H(z), with the scalar convention implicit → explicit nonzero rescalings of canonical representatives, existentially selected together with the positive multiplicities; reason: H has degree two and changes under rescaling; this makes the source normalization explicit while retaining the literal product identity
--   - encoding: the finite epsilon-limit set over the Puiseux field → specializations of actual nonnegative-valuation epsilon-Puiseux solutions in an iterated Hahn ambient field; reason: all finite ramification denominators and infinity points are retained, and no resultant factorization defines the limit set
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Lemma 5.2, p. 21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Resultant

set_option autoImplicit false

namespace APSCounting893.Main

theorem ierardi_resultant_factorization (F : ReducedMap) (D : LineData F) (lambda : Affine ℂ (F.n + 1))
    (hsep : Set.InjOn (separatingForm lambda) (zeroFiber F D.c ∪ {0}))
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees) :
    ∃ S : Finset (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient),
      (S : Set _) = epsilonLimitSet F D.c D.alpha degrees ∧
      ∃ (mu : (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) → ℕ)
        (representatives : (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) →
          (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient)),
        (∀ z ∈ S, 0 < mu z ∧ ∃ a : PuiseuxAmbient, a ≠ 0 ∧ representatives z = a • z) ∧
        trailingEpsilonResultant (resultantFor F D.c D.alpha lambda degrees) =
          ∏ z ∈ S, HAtPoint F lambda (representatives z) ^ mu z := by sorry

end APSCounting893.Main
