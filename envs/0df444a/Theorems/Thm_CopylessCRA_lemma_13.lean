-- Prove2me | Theorems.Thm_CopylessCRA_lemma_13
-- name    : CopylessCRA.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:28.98825+00:00
-- url     : https://prove2.me/theorems/fcacefb0-b975-493d-a01e-c2076ac8c5fc
-- title:
--   Lemma 13, p.10 — $exe$ permutes $S_{ret}$ and $(exe)^{m_0}$ fixes it
-- statement:
--   Let $\delta$ be a complete deterministic control on a finite set $S$. Choose a word $t$ for which $S_{ret}=\delta(S,t)$ has minimum size, let $m_0=|S_{ret}|!$ and $e=t^{m_0}$. Then
--
--   1. $t$ permutes $S_{ret}$;
--   2. $\delta(S,e)=S_{ret}$ and $e$ fixes every state of $S_{ret}$;
--   3. (Lemma 13) for every word $x$, the word $exe$ permutes $S_{ret}$, and $(exe)^{m_0}$ fixes every state of $S_{ret}$.
--
--   Differences from the source:
--   - generalization: words over a (finite) alphabet $\Sigma$ → words over any type $\alpha$ of letters (no finiteness assumed); reason: the statement concerns only the action of words on the finite state set $S$; a finite alphabet is a special case
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), §4 and Lemma 13, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_returnWords

namespace CopylessCRA

/-- **Lemma 13** (with the facts stated before it). Let `t` be a word for which the image
`S_ret = δ(S, t)` has minimum size, `m₀ = |S_ret|!` and `e = t^{m₀}`. Then `t` permutes `S_ret`,
`δ(S, e) = S_ret` and `e`
fixes every state of `S_ret`. For every word `x`, the word `exe` permutes `S_ret`, and `(exe)^{m₀}`
fixes every state of `S_ret`.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), §4 and Lemma 13, p.10 (PDF p.12).

**Formalization Note** The control is any finite state set with a complete deterministic transition
function `δ`; `δ` is extended to words from the left (`deltaWord`). -/
theorem lemma_13 {S α : Type*} [Fintype S] [DecidableEq S] (δ : S → α → S) (t : List α)
    (ht : IsMinImageWord δ t) :
    Set.BijOn (fun s => deltaWord δ s t) (imageWord δ t : Set S) (imageWord δ t : Set S) ∧
    imageWord δ (eWord δ t) = imageWord δ t ∧
    (∀ s ∈ imageWord δ t, deltaWord δ s (eWord δ t) = s) ∧
    ∀ x : List α,
      Set.BijOn (fun s => deltaWord δ s (eWord δ t ++ x ++ eWord δ t))
        (imageWord δ t : Set S) (imageWord δ t : Set S) ∧
      ∀ s ∈ imageWord δ t, deltaWord δ s
        (List.replicate (imageWord δ t).card.factorial (eWord δ t ++ x ++ eWord δ t)).flatten = s := by sorry

end CopylessCRA
