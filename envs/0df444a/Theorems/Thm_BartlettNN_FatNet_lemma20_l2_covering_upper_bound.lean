-- Prove2me | Theorems.Thm_BartlettNN_FatNet_lemma20_l2_covering_upper_bound
-- name    : BartlettNN.FatNet.lemma20_l2_covering_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:49:05.516208+00:00
-- url     : https://prove2.me/theorems/dd4c1fa3-8080-4b48-af2c-606a1f52fcbc
-- title:
--   Lemma 20, (5) — log₂ N_2(F, γ, m) < 1 + d log₂(4emM/(dγ)) log₂(9mM²/γ²), d = fat_F(γ/4)
-- statement:
--   Let $F$ be a class of functions from a set $X$ to $[-M/2,M/2]$, with $M>0$, and let $\gamma>0$. Suppose $d=\operatorname{fat}_F(\gamma/4)$ is finite and $m\in\mathbb N$ satisfies $m\ge 2+2d\log_2(32M/\gamma)$. Then $\mathcal N_2(F,\gamma,m)$ is finite and
--
--   $$
--   \log_2\mathcal N_2(F,\gamma,m)\ <\ 1+d\,\log_2\!\Big(\frac{4emM}{d\gamma}\Big)\log_2\!\Big(\frac{9mM^2}{\gamma^2}\Big).
--   \tag{5}
--   $$
--
--   This upper-bounds the $\ell_2$ covering numbers of the hidden-unit class by its fat-shattering dimension at a finer scale; it is the input from the hidden layer in the proof of Theorem 17.
--
--   **Formalization Note** $M>0$ and $\gamma>0$ are implicit in the paper's $\log_2(32M/\gamma)$ and are stated. The finiteness of $d$ is implicit in "$d=\operatorname{fat}_F(\gamma/4)$". Logarithms are base $2$ (`Real.logb 2`) and $e=\exp(1)$. When $d=0$ the product term is $0$ (Lean's $0\cdot\log_2(\cdot/0)=0$), so the bound reads $\log_2\mathcal N_2<1$, which is the paper's reading.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 532, Lemma 20, Eq. (5)

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_FatNet_coverNum

namespace BartlettNN.FatNet

/-- **Lemma 20, inequality (5)** (Bartlett 1998, p. 532).
Let `F` be a class of `[−M/2, M/2]`-valued functions on `X`. If `d = fat_F(γ/4)` and
`m ≥ 2 + 2d log₂(32M/γ)`, then `N_2(F, γ, m)` is finite and
`log₂ N_2(F, γ, m) < 1 + d log₂(4emM/(dγ)) log₂(9mM²/γ²)`.
The hypotheses `0 < M` and `0 < γ` are implicit in the paper's `log₂(32M/γ)`. -/
theorem lemma20_l2_covering_upper_bound {X : Type*} (F : Set (X → ℝ)) (M γ : ℝ) (d m : ℕ)
    (hM : 0 < M) (hγ : 0 < γ)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2))
    (hd : BartlettNN.Margin.fat F (γ / 4) = d)
    (hm : 2 + 2 * (d : ℝ) * Real.logb 2 (32 * M / γ) ≤ (m : ℝ)) :
    ∃ N : ℕ, N2 F γ m = N ∧
      Real.logb 2 N < 1 + (d : ℝ) * Real.logb 2 (4 * Real.exp 1 * m * M / (d * γ)) *
        Real.logb 2 (9 * m * M ^ 2 / γ ^ 2) := by sorry

end BartlettNN.FatNet
