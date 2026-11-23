-- Prove2me | Theorems.Thm_ContentStyle_content_only_of_invariance
-- name    : ContentStyle.content_only_of_invariance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:12:32.525179+00:00
-- url     : https://prove2.me/theorems/ae6f7ef2-f8d7-40cd-bed1-5431d7b515fa
-- title:
--   Theorem 4.2, Step 2: an a.s. invariant smooth map depends on content only
-- statement:
--   Let $\mathcal Z=\mathcal C\times\mathcal S$ be open and simply connected, and let $(p_z,p_A,p_{\tilde s\mid s,A})$ satisfy Assumptions 3.1–3.2 and conditions (ii) and (iii) of Theorem 4.2. Let $h_c:\mathcal Z\to\mathbb{R}^{n_c}$ be smooth, and suppose
--
--   $$h_c(z)=h_c(\tilde z)\qquad\text{almost surely for }(z,\tilde z)\sim p.$$
--
--   Then $h_c$ depends on the content only:
--
--   $$h_c(c,s)=h_c(c,s')\qquad\text{for all }c\in\mathcal C,\ s,s'\in\mathcal S.$$
--
--   This is Step 2 of the proof of Theorem 4.2, which is used again in the proofs of Theorems 4.3 and 4.4.
--
--   **Formalization Note** The paper concludes that every partial derivative $\partial h_c/\partial s_l$ vanishes. The Lean conclusion is the paper's restatement, that $h_c$ is a function of $c$ alone.
-- source:
--   von Kügelgen, Sharma, Gresele, Brendel, Schölkopf, Besserve and Locatello, Self-Supervised Learning with Data Augmentations Provably Isolates Content from Style, NeurIPS 2021, arXiv:2106.04619v4, Appendix A.1, proof of Theorem 4.2, Step 2, eqs. (9)-(20), pp. 18-19 (used again in the proofs of Theorems 4.3 and 4.4)

import Mathlib
import Definitions.Def_ContentStyle_Basic

open MeasureTheory
open scoped ContDiff

namespace ContentStyle

theorem content_only_of_invariance {nc ns : ℕ}
    (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ)) (hZ : IsLatentSpace C S)
    (M : LatentModel nc ns) (hM : IsAugModel C S M) (hii : CondII C S M) (hiii : CondIII S M)
    (hc : Latent nc ns → (Fin nc → ℝ)) (hsmooth : ContDiffOn ℝ ∞ hc (C ×ˢ S))
    (hinv : pairProb C S M {w | hc w.1 ≠ hc w.2} = 0) :
    ∀ c ∈ C, ∀ s ∈ S, ∀ s' ∈ S, hc (c, s) = hc (c, s') := by sorry

end ContentStyle
