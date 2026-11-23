-- Prove2me | Theorems.Thm_ContentStyle_alignMaxEnt_global_minimum
-- name    : ContentStyle.alignMaxEnt_global_minimum
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:15:34.442898+00:00
-- url     : https://prove2.me/theorems/b0b47a06-c15f-422d-82ed-55dab5f0b80a
-- title:
--   Claim A.1 (as proved): the global minimum of $L_{\mathrm{AlignMaxEnt}}$ is $0$, attained by a function of the content
-- statement:
--   Assume the setting and conditions (i)–(iii) of Theorem 4.2, with $1\le n_c$ and $1\le n_s$. Then:
--
--   1. $L_{\mathrm{AlignMaxEnt}}(g)\ge0$ for every $g:\mathcal X\to(0,1)^{n_c}$;
--   2. there is a measurable $d:\mathcal C\to(0,1)^{n_c}$ (the Darmois construction) such that $g^\star=d\circ f^{-1}_{1:n_c}$ satisfies
--
--   $$L_{\mathrm{AlignMaxEnt}}(g^\star)=0.$$
--
--   So the global minimum of $L_{\mathrm{AlignMaxEnt}}$ is $0$, and it is attained by a function of the content.
--
--   **Formalization Note** Claim A.1 and the text before it also assert that $d$, and hence $g^\star$, is smooth, because $p_z$ is smooth. The proof does not establish this: the content marginal $p_c(c)=\int p_z(c,s)\,ds$ of a smooth $p_z$ need not be continuous. This statement keeps what the proof establishes and asks for a measurable $d$. The entropy is $-\infty$ (and the loss $+\infty$) when $g(x)$ has no density.
-- source:
--   von Kügelgen, Sharma, Gresele, Brendel, Schölkopf, Besserve and Locatello, Self-Supervised Learning with Data Augmentations Provably Isolates Content from Style, NeurIPS 2021, arXiv:2106.04619v4, Appendix A.3, proof of Theorem 4.4, Step 1 and Claim A.1, eqs. (24)-(28), pp. 20-21

import Mathlib
import Definitions.Def_ContentStyle_Basic

open MeasureTheory
open scoped ContDiff

namespace ContentStyle

theorem alignMaxEnt_global_minimum {nc ns d : ℕ} (hnc : 1 ≤ nc) (hns : 1 ≤ ns)
    (C : Set (Fin nc → ℝ)) (S : Set (Fin ns → ℝ)) (hZ : IsLatentSpace C S)
    (M : LatentModel nc ns) (f : Latent nc ns → Obs d)
    (hM : IsAugModel C S M) (hi : CondI C S f) (hii : CondII C S M) (hiii : CondIII S M) :
    (∀ g : Obs d → (Fin nc → ℝ), Set.MapsTo g (f '' (C ×ˢ S)) (cube nc) →
      0 ≤ alignMaxEntLoss C S M f g) ∧
    ∃ dm : (Fin nc → ℝ) → (Fin nc → ℝ), Measurable dm ∧ Set.MapsTo dm C (cube nc) ∧
      alignMaxEntLoss C S M f (fun x => dm (Function.invFunOn f (C ×ˢ S) x).1) = 0 := by sorry

end ContentStyle
