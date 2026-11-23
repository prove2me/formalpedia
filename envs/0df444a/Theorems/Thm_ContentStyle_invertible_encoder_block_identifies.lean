-- Prove2me | Theorems.Thm_ContentStyle_invertible_encoder_block_identifies
-- name    : ContentStyle.invertible_encoder_block_identifies
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:14:36.95017+00:00
-- url     : https://prove2.me/theorems/870e525c-49b7-47c1-8d9b-1f2e18295862
-- title:
--   Theorem 4.3: identifying content with an invertible encoder
-- statement:
--   Assume the setting and conditions (i)–(iii) of Theorem 4.2 for the true process, with $1\le n_c$ and $1\le n_s$. Let $g:\mathcal X\to\mathcal Z$ be a smooth bijection that minimises
--
--   $$L_{\mathrm{Align}}(g)=\mathbb E_{(x,\tilde x)\sim p_{x,\tilde x}}\big\|g(x)_{1:n_c}-g(\tilde x)_{1:n_c}\big\|_2^2$$
--
--   over all smooth bijections $\mathcal X\to\mathcal Z$. Then $g$ block-identifies the true content: $g(f(c,s))_{1:n_c}=h(c)$ on $\mathcal Z$ for some $h$ injective on $\mathcal C$.
--
--   **Formalization Note** The theorem refers to "conditions (i)–(iv) as in Theorem 4.2", but Theorem 4.2 has only conditions (i)–(iii), and those three are assumed here. "Smooth and invertible" is read as a smooth bijection of $\mathcal X$ onto $\mathcal Z$, and the minimisation is over that class, which contains $f^{-1}$.
-- source:
--   von Kügelgen, Sharma, Gresele, Brendel, Schölkopf, Besserve and Locatello, Self-Supervised Learning with Data Augmentations Provably Isolates Content from Style, NeurIPS 2021, arXiv:2106.04619v4, Section 4.2, Theorem 4.3, eq. (4), p. 6; proof in Appendix A.2, pp. 19-20

import Mathlib
import Definitions.Def_ContentStyle_Basic

open MeasureTheory
open scoped ContDiff

namespace ContentStyle

theorem invertible_encoder_block_identifies {nc ns d : ℕ} (hnc : 1 ≤ nc) (hns : 1 ≤ ns)
    (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ)) (hZ : IsLatentSpace C S)
    (M : LatentModel nc ns) (f : Latent nc ns → Obs d)
    (hM : IsAugModel C S M) (hi : CondI C S f) (hii : CondII C S M) (hiii : CondIII S M)
    (g : Obs d → Latent nc ns) (hg : IsSmoothInvertible C S f g)
    (hmin : ∀ g' : Obs d → Latent nc ns, IsSmoothInvertible C S f g' →
      alignLoss C S M f g ≤ alignLoss C S M f g') :
    BlockIdentifies C S f (fun x => (g x).1) := by sorry

end ContentStyle
