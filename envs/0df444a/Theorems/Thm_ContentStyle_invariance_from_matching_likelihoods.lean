-- Prove2me | Theorems.Thm_ContentStyle_invariance_from_matching_likelihoods
-- name    : ContentStyle.invariance_from_matching_likelihoods
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:11:56.626285+00:00
-- url     : https://prove2.me/theorems/42677226-e5f5-4dba-b6cf-023b468a4a47
-- title:
--   Theorem 4.2, Step 1: matching likelihoods force content invariance (eq. (9))
-- statement:
--   Let $(p_z,p_A,p_{\tilde s\mid s,A},f)$ be the true generative process and $(\hat p_z,\hat p_A,\hat p_{\tilde s\mid s,A},\hat f)$ a model on the same space $\mathcal Z=\mathcal C\times\mathcal S$. Both satisfy Assumptions 3.1–3.2 and condition (i), and $\hat f(\mathcal Z)=f(\mathcal Z)$. Suppose that the laws of the observed pairs agree, $p_{x,\tilde x}=\hat p_{x,\tilde x}$. Then $h=\hat f^{-1}\circ f$ satisfies
--
--   $$h(z)_{1:n_c}=h(\tilde z)_{1:n_c}\qquad\text{almost surely for }(z,\tilde z)\sim p.$$
--
--   This is the invariance (9), the first step of the proof of Theorem 4.2.
--
--   **Formalization Note** Matching likelihoods $p_{x,\tilde x}=\hat p_{x,\tilde x}$ on $\mathcal X\times\mathcal X$ is stated as equality of the two laws on every Borel set of $\mathbb{R}^d\times\mathbb{R}^d$. The pair $(x,\tilde x)$ has no density with respect to Lebesgue measure on $\mathcal X\times\mathcal X$, because $\tilde c=c$.
-- source:
--   von Kügelgen, Sharma, Gresele, Brendel, Schölkopf, Besserve and Locatello, Self-Supervised Learning with Data Augmentations Provably Isolates Content from Style, NeurIPS 2021, arXiv:2106.04619v4, Appendix A.1, proof of Theorem 4.2, Step 1, eqs. (6)-(9), pp. 17-18

import Mathlib
import Definitions.Def_ContentStyle_Basic

open MeasureTheory
open scoped ContDiff

namespace ContentStyle

theorem invariance_from_matching_likelihoods {nc ns d : ℕ}
    (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ))
    (M Mhat : LatentModel nc ns) (f fhat : Latent nc ns → Obs d)
    (hM : IsAugModel C S M) (hMhat : IsAugModel C S Mhat)
    (hf : CondI C S f) (hfhat : CondI C S fhat)
    (hX : fhat '' (C ×ˢ S) = f '' (C ×ˢ S))
    (hmatch : ∀ E : Set (Obs d × Obs d), MeasurableSet E →
      obsPairProb C S M f E = obsPairProb C S Mhat fhat E) :
    pairProb C S M {w | (Function.invFunOn fhat (C ×ˢ S) (f w.1)).1 ≠
      (Function.invFunOn fhat (C ×ˢ S) (f w.2)).1} = 0 := by sorry

end ContentStyle
