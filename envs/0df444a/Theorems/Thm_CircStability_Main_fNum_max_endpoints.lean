-- Prove2me | Theorems.Thm_CircStability_Main_fNum_max_endpoints
-- name    : CircStability.Main.fNum_max_endpoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:39.324442+00:00
-- url     : https://prove2.me/theorems/148853ac-7486-4c1c-a513-9f19b9b9f3aa
-- title:
--   §2.1, p. 6 — k ↦ f(n, k, c) is convex, so its maximum over [a, b] is attained at an endpoint
-- statement:
--   Fix $n$ and $c$ with $c\le n$. The function $k\mapsto f(n,k,c)=\binom{c-k+1}{2}+k(n-c+k-1)$ is convex in $k$, so its maximum over an interval is attained at an endpoint: for all integers $0\le a\le k\le b\le c$,
--
--   $$
--   f(n,k,c)\le\max\{f(n,a,c),\,f(n,b,c)\}.
--   $$
--
--   This is the monotonicity fact used in the proof of Lemma 4.3: a value $f(n,s,c)$ with $k+1\le s\le\lfloor c/2\rfloor-1$ never exceeds $\max\{f(n,k+1,c),f(n,\lfloor c/2\rfloor-1,c)\}$.
--
--   **Formalization Note.** The page states the convexity through the closed form $f(n,k,c)=\frac32\big[k^2-(\frac{4c-2n}{3}+1)k\big]+\frac{c^2+c}{2}$; the formal statement records the consequence the paper uses, over integer $k$. The bound $b\le c$ keeps every natural-number subtraction in $f$ exact.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 6, §2.1, last paragraph (convexity of f(n, k, c) in k)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
open Finset SimpleGraph

namespace CircStability.Main

theorem fNum_max_endpoints (n c a b k : ℕ) (hcn : c ≤ n) (hbc : b ≤ c)
    (hak : a ≤ k) (hkb : k ≤ b) :
    fNum n k c ≤ max (fNum n a c) (fNum n b c) := by sorry

end CircStability.Main
