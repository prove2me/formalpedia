-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_cubic_root_lipschitz
-- name    : CountingLLL.ContractedWalk.cubic_root_lipschitz
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:11:38.912197+00:00
-- url     : https://prove2.me/theorems/b87a1c2b-33f3-47b6-8098-4955e1bd0e8d
-- title:
--   Lipschitz bound for the admissible cubic root
-- statement:
--   For $0\le\theta<1/3$, two admissible roots $g,h\in[0,1]$ of $r=1-\theta+\theta z r^3$ at parameters $x,y\in[0,1]$ satisfy $|g-h|\le\theta|x-y|/(1-3\theta)$. This gives continuity of the contracted-walk generating function needed for the source’s change of variables.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

theorem CountingLLL.ContractedWalk.cubic_root_lipschitz (θ x y g h : ℝ) (ht0 : 0 ≤ θ) (ht : θ < 1/3)
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 ≤ y) (hy : y ≤ 1)
    (hg0 : 0 ≤ g) (hg : g ≤ 1) (hh0 : 0 ≤ h) (hh : h ≤ 1)
    (hgEq : g = 1-θ+θ*x*g^3) (hhEq : h = 1-θ+θ*y*h^3) :
    |g-h| ≤ θ/(1-3*θ)*|x-y| := by sorry
