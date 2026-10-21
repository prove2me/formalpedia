-- Prove2me | Theorems.Thm_EFXGenVal_TwoVal_lemma_5
-- name    : EFXGenVal.TwoVal.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:58.566923+00:00
-- url     : https://prove2.me/theorems/7ad48e54-3e98-4246-831d-9b91d0ca6e95
-- title:
--   Lemma 5, p. 8 — a non-envious g-champion of j, with neither agent a self g-champion, g-decomposes j
-- statement:
--   Let the agents have normalized, monotone, non-degenerate valuations, let $X$ be an allocation, and let $g$ be an unallocated item. Suppose agent $i$ $g$-champions agent $j$ (that is, $i$ is a most envious agent for $X_j\cup\{g\}$), $i$ does not envy $j$, and neither $i$ nor $j$ is a self $g$-champion. Then $i$ $g$-decomposes $j$: every minimum preferred set $P$ of $i$ for $X_j\cup\{g\}$ satisfies
--   $$\{g\}\subsetneq P\subsetneq X_j\cup\{g\}.$$
--
--   The lemma identifies a typical situation in which the bundle $X_j$ splits into a top half $P\setminus\{g\}$ and a bottom half $(X_j\cup\{g\})\setminus P$; the proof of Theorem 14 uses it with $i=a_0$, $j=b_0$.
--
--   **Formalization Note** "$i$ $g$-decomposes $j$" is formalized for every minimum preferred set $P$, the stronger reading of the page's "where $P$ is a minimum preferred set"; the page's proof starts from an arbitrary such $P$.
-- source:
--   Mahara, Extension of Additive Valuations to General Valuations on the Existence of EFX, arXiv:2107.09901v2, §2.3, Lemma 5, p. 8

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

namespace EFXGenVal.TwoVal

open LittleCharity.EFX

theorem lemma_5 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X)
    (g : Fin m) (hg : g ∈ pool X) (i j : Fin n)
    (hij : Champions v X g i j) (hne : ¬ Envies v X i j)
    (hi : ¬ Champions v X g i i) (hj : ¬ Champions v X g j j) :
    Decomposes v X g i j := by sorry

end EFXGenVal.TwoVal
