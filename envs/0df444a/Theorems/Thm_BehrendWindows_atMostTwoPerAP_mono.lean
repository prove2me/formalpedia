-- Prove2me | Theorems.Thm_BehrendWindows_atMostTwoPerAP_mono
-- name    : BehrendWindows.atMostTwoPerAP_mono
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-21T01:48:26.786306+00:00
-- url     : https://prove2.me/theorems/cca38364-daad-49ea-abb5-10ce2556a8ab
-- title:
--   Monotonicity of $m$-sparseness
-- statement:
--   Let $T,T'\subset\mathbb{Z}$ be finite, $c\in\mathbb{Z}$ and $m'\le m$. If $T$ is $m$-sparse and
--
--   $$T'\subseteq T+c=\{t+c: t\in T\},$$
--
--   then $T'$ is $m'$-sparse.
--
--   In one statement this says that $m$-sparseness passes to subsets ($c=0$), to translates ($T'=T+c$) and to shorter progressions ($m'\le m$).
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, milestone 5

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP

namespace BehrendWindows

theorem atMostTwoPerAP_mono {T T' : Finset ℤ} {m m' : ℕ} (c : ℤ)
    (hT : T' ⊆ T.image (· + c)) (hm : m' ≤ m) (h : AtMostTwoPerAP T m) :
    AtMostTwoPerAP T' m' := by sorry

end BehrendWindows
