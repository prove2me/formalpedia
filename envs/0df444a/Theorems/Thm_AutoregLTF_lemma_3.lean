-- Prove2me | Theorems.Thm_AutoregLTF_lemma_3
-- name    : AutoregLTF.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:33.959929+00:00
-- url     : https://prove2.me/theorems/c093fa24-a793-43ce-b7aa-df9d16bf0e30
-- title:
--   Lemma 3, p.12 — the $m^2$ label-free prompts (35) are distinct and shattered by $\mathcal F_{d,T}$
-- statement:
--   Let $m\ge2$ and $p=378(m+2)$. If $d\ge p+1$ and $T\ge(m+3)p$, then the $m^2$ prompts $x^{i,s}\in\{0,1\}^d$ ($i,s\in[m]$) of (35) are pairwise distinct, and the set they form is shattered by $\mathcal F_{d,T}$: for every labeling of these $m^2$ prompts by $\{0,1\}$ there is $w\in\mathbb Q^d$ with $f^T_w$ realizing it.
--
--   Consequently $\mathrm{VCdim}(\mathcal F_{d,T})\ge m^2$ under these conditions.
--
--   Differences from the source:
--   - encoding: "distinct" → injectivity of (i, s) ↦ x^{i,s} on [m] × [m]; reason: same statement
--   - encoding: the prompts (35), built "for each fixed encoding θ" → prompt m d T i s, built from the blocks of the all-zero labeling; reason: by Lemma 1 the blocks E^0, E^1 are the same for every labeling; the paper notes the prompts are independent of the labels
--   - encoding: "shattered by F_{d,T}" → QAlgorithms.Learning.ShattersSet (cls d T) of the finite image of [m] × [m]; reason: the published shattering predicate is the paper's definition (p.2)
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), Lemma 3, p.12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
import Definitions.Def_AutoregLTF_prompt

namespace AutoregLTF

/-- **Lemma 3**, p.12 (PDF p.12).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"For `d ≥ p + 1` and `T ≥ (m + 3)p`, the `m²` prompts in (35) are distinct and shattered by
`F_{d,T}`."

**Formalization Note.** `m ≥ 2` is the standing assumption (p.4). The prompts `x^{i,s}`
(`i, s ∈ [m]`) are `prompt m d T i s`, built from the label-free blocks (Lemma 1). "Distinct" is
injectivity of `(i, s) ↦ x^{i,s}` on `[m] × [m]`; "shattered" is `QAlgorithms.Learning.ShattersSet`
(every labeling of the finite set of prompts is realized by some `f ∈ F_{d,T}`), applied to the image of
`[m] × [m]`. -/
theorem lemma_3 (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : p m + 1 ≤ d) (T : ℕ)
    (hT : (m + 3) * p m ≤ T) :
    (∀ i ∈ Finset.Icc 1 m, ∀ s ∈ Finset.Icc 1 m, ∀ i' ∈ Finset.Icc 1 m, ∀ s' ∈ Finset.Icc 1 m,
      prompt m d T i s = prompt m d T i' s' → i = i' ∧ s = s') ∧
    QAlgorithms.Learning.ShattersSet (cls d T)
      ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).image (fun q => prompt m d T q.1 q.2)) := by sorry

end AutoregLTF
