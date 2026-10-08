-- Prove2me | Theorems.Thm_BartlettNN_FatNet_lemma19_l1_covering_lower_bound
-- name    : BartlettNN.FatNet.lemma19_l1_covering_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:49:07.125897+00:00
-- url     : https://prove2.me/theorems/14ba9a62-3249-4f4b-a422-434a9925a76e
-- title:
--   Lemma 19 — log₂ N_1(F, γ, d) ≥ d/32 when fat_F(4γ) ≥ d
-- statement:
--   Let $F$ be a class of functions from a set $X$ to $[0,1]$, let $\gamma\in\mathbb R$ and $d\in\mathbb N$, and suppose $\operatorname{fat}_F(4\gamma)\ge d$. Then the $\ell_1$ covering number of $F$ at scale $\gamma$ on samples of length $d$ satisfies
--
--   $$
--   \log_2\mathcal N_1(F,\gamma,d)\ \ge\ \frac d{32}.
--   $$
--
--   This is a lower bound on covering numbers in terms of the fat-shattering dimension: a large shattered set forces many well-separated functions on it. In the proof of Theorem 17 it is combined with upper bounds on covering numbers to bound the fat-shattering dimension. The paper cites it from Bartlett, Kulkarni and Posner (it is implicit in the proof of their Theorem 2) and does not prove it.
--
--   **Formalization Note** The conclusion is stated for every finite value $N$ of $\mathcal N_1(F,\gamma,d)$: if $\mathcal N_1(F,\gamma,d)=N\in\mathbb N$ then $d/32\le\log_2 N$. When the covering number is infinite the lower bound holds trivially. The hypothesis $\gamma>0$ is not needed: for $\gamma\le0$ and $F$ nonempty no finite cover exists.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 532, Lemma 19 (cited from [6])

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_FatNet_coverNum

namespace BartlettNN.FatNet

/-- **Lemma 19** (Bartlett 1998, p. 532; cited from Bartlett–Kulkarni–Posner [6]).
If `F` is a class of `[0, 1]`-valued functions on `X` with `fat_F(4γ) ≥ d`, then
`log₂ N_1(F, γ, d) ≥ d/32`. The covering number is stated for every finite value `N`; when
`N_1(F, γ, d) = ⊤` the lower bound holds trivially. -/
theorem lemma19_l1_covering_lower_bound {X : Type*} (F : Set (X → ℝ)) (γ : ℝ) (d : ℕ)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfat : (d : ℕ∞) ≤ BartlettNN.Margin.fat F (4 * γ)) :
    ∀ N : ℕ, N1 F γ d = N → (d : ℝ) / 32 ≤ Real.logb 2 N := by sorry

end BartlettNN.FatNet
