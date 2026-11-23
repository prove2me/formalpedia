-- Prove2me | Theorems.Thm_ContentStyle_alignMaxEnt_minimiser_content_uniform
-- name    : ContentStyle.alignMaxEnt_minimiser_content_uniform
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:16:25.977648+00:00
-- url     : https://prove2.me/theorems/536fc54a-4e9f-4c30-a5c4-21a72ea2c1bd
-- title:
--   Theorem 4.4, Steps 1-2 (as proved): a zero-loss smooth encoder is a function of content with uniform law
-- statement:
--   Assume the setting and conditions (i)–(iii) of Theorem 4.2, with $1\le n_c$ and $1\le n_s$. Let $g:\mathcal X\to(0,1)^{n_c}$ be smooth with
--
--   $$L_{\mathrm{AlignMaxEnt}}(g)=\mathbb E\,\|g(x)-g(\tilde x)\|_2^2-H(g(x))=0,$$
--
--   which by Claim A.1 is the global minimum. Then:
--
--   1. $g(f(c,s))=g(f(c,s'))$ for all $c\in\mathcal C$ and $s,s'\in\mathcal S$, so $\hat c=g(x)=h(c)$ depends on the content only;
--   2. $g(x)$ is uniformly distributed on $(0,1)^{n_c}$.
--
--   **Formalization Note** This is Steps 1–2 of the proof of Theorem 4.4 (eqs. (29)–(31)), stated as proved there. The proof treats a minimiser as a function with $L_{\mathrm{AlignMaxEnt}}(g)=0$. Step 3 of the proof, the invertibility of $h$, rests on Proposition A.2, which is false. Theorem 4.4 itself is false (see the mission description), so it is not stated.
-- source:
--   von Kügelgen, Sharma, Gresele, Brendel, Schölkopf, Besserve and Locatello, Self-Supervised Learning with Data Augmentations Provably Isolates Content from Style, NeurIPS 2021, arXiv:2106.04619v4, Section 4.2, Theorem 4.4, eq. (5), p. 7; Appendix A.3, Steps 1-2, eqs. (29)-(31), p. 21

import Mathlib
import Definitions.Def_ContentStyle_Basic

open MeasureTheory
open scoped ContDiff

namespace ContentStyle

theorem alignMaxEnt_minimiser_content_uniform {nc ns d : ℕ} (hnc : 1 ≤ nc) (hns : 1 ≤ ns)
    (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ)) (hZ : IsLatentSpace C S)
    (M : LatentModel nc ns) (f : Latent nc ns → Obs d)
    (hM : IsAugModel C S M) (hi : CondI C S f) (hii : CondII C S M) (hiii : CondIII S M)
    (g : Obs d → (Fin nc → ℝ)) (hg : SmoothOnSet (f '' (C ×ˢ S)) g)
    (hcube : Set.MapsTo g (f '' (C ×ˢ S)) (cube nc))
    (hzero : alignMaxEntLoss C S M f g = 0) :
    (∀ c ∈ C, ∀ s ∈ S, ∀ s' ∈ S, g (f (c, s)) = g (f (c, s'))) ∧
      (latentLaw C S M).map (fun z => g (f z)) = volume.restrict (cube nc) := by sorry

end ContentStyle
