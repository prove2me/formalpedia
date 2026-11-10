-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_avoiding_minor
-- name    : BhangaleHypergraph.Main.avoiding_minor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:06:06.713464+00:00
-- url     : https://prove2.me/theorems/524d1227-ae5b-44ac-8bd4-2229f78e958d
-- title:
--   Lemma 2.14 — Avoidance under exact minors
-- statement:
--   Let $W,W'$ be test domains on positive label sets, $f:W\to[C]$ and $g:W'\to[C]$, and let $\pi$ be any total map giving an exact minor identity $g(B)=f(\pi^{-1}B)$ on $W'$, including the required inverse-image closure. For every set of colors $T$ and every $T$-avoiding set $S$ for $f$,
--   $$\pi(S)\text{ is }T\text{-avoiding for }g.$$
--   Neither membership of $S$ in $W$ nor surjectivity of $\pi$ is required.
--
--   This transports avoidance certificates across the exact minors.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 2.14, p. 10 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Restricted

namespace BhangaleHypergraph.Main

theorem avoiding_minor {R R' C : ℕ} (hR : 1 ≤ R) (hR' : 1 ≤ R') (hC : 2 ≤ C)
    {W : Finset (Finset (Fin R))} {W' : Finset (Finset (Fin R'))}
    (hW : TestDomain W) (hW' : TestDomain W') (f : W → Fin C) (g : W' → Fin C)
    (π : Fin R → Fin R') (hminor : ExactMinor f g π)
    (S : Finset (Fin R)) (T : Finset (Fin C)) (hS : Avoids f S T) :
    Avoids g (S.image π) T := by sorry

end BhangaleHypergraph.Main
