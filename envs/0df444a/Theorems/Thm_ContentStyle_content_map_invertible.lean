-- Prove2me | Theorems.Thm_ContentStyle_content_map_invertible
-- name    : ContentStyle.content_map_invertible
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:13:06.832639+00:00
-- url     : https://prove2.me/theorems/d2507ec8-7010-4fa1-b050-4fbbd58d72c4
-- title:
--   Theorem 4.2, end of Step 2: the content block of an invertible map is invertible
-- statement:
--   Let $\mathcal Z=\mathcal C\times\mathcal S$ be open and simply connected, and let $h:\mathcal Z\to\mathcal Z$ be a smooth bijection whose content block $h(c,s)_{1:n_c}$ does not depend on $s$. Then there is a smooth bijection $h_c:\mathcal C\to\mathcal C$ with
--
--   $$h(c,s)_{1:n_c}=h_c(c)\qquad\text{for all }(c,s)\in\mathcal Z.$$
--
--   This is the final sentence of Step 2 of the proof of Theorem 4.2: smoothness and invertibility of $h_c$ follow from those of $h$.
--
--   **Formalization Note** The paper's $h$ is $\hat f^{-1}\circ f$ in Theorem 4.2 and $g\circ f$ in Theorem 4.3. The statement assumes only that $h$ is a smooth bijection of $\mathcal Z$, which covers both cases.
-- source:
--   von Kügelgen, Sharma, Gresele, Brendel, Schölkopf, Besserve and Locatello, Self-Supervised Learning with Data Augmentations Provably Isolates Content from Style, NeurIPS 2021, arXiv:2106.04619v4, Appendix A.1, proof of Theorem 4.2, last paragraph of Step 2, p. 19

import Mathlib
import Definitions.Def_ContentStyle_Basic

open MeasureTheory
open scoped ContDiff

namespace ContentStyle

theorem content_map_invertible {nc ns : ℕ}
    (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ)) (hZ : IsLatentSpace C S)
    (h : Latent nc ns → Latent nc ns) (hsmooth : ContDiffOn ℝ ∞ h (C ×ˢ S))
    (hbij : Set.BijOn h (C ×ˢ S) (C ×ˢ S))
    (hcontent : ∀ c ∈ C, ∀ s ∈ S, ∀ s' ∈ S, (h (c, s)).1 = (h (c, s')).1) :
    ∃ hc : (Fin nc → ℝ) → (Fin nc → ℝ), Set.BijOn hc C C ∧ ContDiffOn ℝ ∞ hc C ∧
      ∀ z ∈ C ×ˢ S, (h z).1 = hc z.1 := by sorry

end ContentStyle
