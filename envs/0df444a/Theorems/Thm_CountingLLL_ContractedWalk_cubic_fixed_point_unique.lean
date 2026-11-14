-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_cubic_fixed_point_unique
-- name    : CountingLLL.ContractedWalk.cubic_fixed_point_unique
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:07:00.260032+00:00
-- url     : https://prove2.me/theorems/e7b06266-49aa-4313-91f9-9d62232b104d
-- title:
--   Uniqueness of the contracted-walk generating-function root
-- statement:
--   For $0\le\theta<1/3$ and $0\le z\le1$, the equation $g=1-\theta+\theta z g^3$ has at most one solution $g$ in $[0,1]$. This identifies the probability generating function as the unique admissible branch of the paper’s cubic equation.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

theorem CountingLLL.ContractedWalk.cubic_fixed_point_unique (θ z g h : ℝ) (ht0 : 0 ≤ θ) (ht : θ < 1/3)
    (hz0 : 0 ≤ z) (hz : z ≤ 1) (hg0 : 0 ≤ g) (hg : g ≤ 1) (hh0 : 0 ≤ h) (hh : h ≤ 1)
    (hgEq : g = 1-θ+θ*z*g^3) (hhEq : h = 1-θ+θ*z*h^3) : g = h := by sorry
