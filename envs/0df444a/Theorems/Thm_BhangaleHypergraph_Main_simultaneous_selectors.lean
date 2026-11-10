-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_simultaneous_selectors
-- name    : BhangaleHypergraph.Main.simultaneous_selectors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:06:07.232421+00:00
-- url     : https://prove2.me/theorems/b21a32fb-6274-40f3-87d8-f9f7adb16173
-- title:
--   Lemma 3.3 — Simultaneous compatible selectors
-- statement:
--   Fix $C\ge2$, $s=C^{C-1}$ and $d=(2C)^C$. Simultaneously for every positive $R$, every core-containing test domain $W$ and every admissible coloring $f:W\to[C]$, there are choices of $\tau(f)\in\{0,\ldots,C-1\}$ and a nonempty set $\operatorname{Sel}(f)\subseteq[R]$ of size at most $d$. These choices have the universal compatibility property
--   $$f\xrightarrow{\pi}g,\quad\tau(f)=\tau(g)\quad\Longrightarrow\quad\pi(\operatorname{Sel}(f))\cap\operatorname{Sel}(g)\ne\varnothing.$$
--   Choices are fixed before any minor or pair is tested.
--
--   This is the simultaneous selector theorem, with its complete domain of colorings.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: simultaneous choices for every admissible coloring on every core-containing domain → dependent functions on the structure CoreColoring C; reason: the structure contains precisely the domain, positivity and admissibility conditions and no selector properties
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 3.3, p. 15 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Restricted

namespace BhangaleHypergraph.Main

theorem simultaneous_selectors (C : ℕ) (hC : 2 ≤ C) :
    ∃ (τ : CoreColoring C → Fin C) (Sel : (f : CoreColoring C) → Finset (Fin f.R)),
      (∀ f, (Sel f).Nonempty ∧ (Sel f).card ≤ (2 * C) ^ C) ∧
      ∀ (f g : CoreColoring C) (π : Fin f.R → Fin g.R),
        ExactMinor f.color g.color π → τ f = τ g →
          ((Sel f).image π ∩ Sel g).Nonempty := by sorry

end BhangaleHypergraph.Main
