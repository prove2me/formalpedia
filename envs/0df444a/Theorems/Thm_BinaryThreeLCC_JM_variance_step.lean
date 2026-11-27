-- Prove2me | Theorems.Thm_BinaryThreeLCC_JM_variance_step
-- name    : BinaryThreeLCC.JM.variance_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:02:30.103009+00:00
-- url     : https://prove2.me/theorems/cc118747-4402-4a96-ba1d-514b55123cf3
-- title:
--   One-step variance contraction for a lazy random-matrix walk (Lemma 5.7 step)
-- statement:
--   Let $\Omega$ and $\Lambda$ be finite sets, $m=|\Omega|$, $N=|\Lambda|$, and let $\rho:\Lambda\times\Omega\to\Omega$ be such that every $u\in\Omega$ has exactly $N$ preimages, $|\{(a,j):\rho_a(j)=u\}|=N$ (the averaged transition is doubly stochastic). Suppose that for some real $\gamma$ the Poincaré inequality
--
--   $$4N\gamma\sum_i h(i)^2\ \le\ \sum_{i}\sum_{a}\bigl(h(i)-h(\rho_a(i))\bigr)^2$$
--
--   holds for every $h:\Omega\to\mathbb R$ with $\sum_i h(i)=0$. Then for every $g:\Omega\to\mathbb R$, writing $\bar x=\frac1m\sum_j x_j$,
--
--   $$\sum_{a\in\Lambda}\sum_{j}\Bigl(g(j)+g(\rho_a(j))-\overline{g+g\circ\rho_a}\Bigr)^2\ \le\ 4N(1-\gamma)\sum_j\bigl(g(j)-\bar g\bigr)^2 .$$
--
--   Here $j\mapsto\frac12\bigl(g(j)+g(\rho_a(j))\bigr)$ is one lazy step of the random matrix $M_a$, so this is the inequality $\mathbb E_a\,\mathcal E(XM_a)\le(1-\gamma)\,\mathcal E(X)$ from the proof of Lemma 5.7, applied row by row.
-- source:
--   Janzer–Manohar, Reed–Muller Codes are Optimal Binary Linear 3-Query LCCs, STOC 2027 submission #732, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf, Lemma 5.7 and its proof §5.2 (printed pp. 15, 18–20)

import Mathlib

set_option autoImplicit false

namespace BinaryThreeLCC.JM

theorem variance_step {Ω Λ : Type} [Fintype Ω] [Fintype Λ] [DecidableEq Ω]
    (ρ : Λ → Ω → Ω)
    (hdbl : ∀ u, (Finset.univ.filter (fun p : Λ × Ω => ρ p.1 p.2 = u)).card = Fintype.card Λ)
    (γ : ℝ) (hpoinc : ∀ h : Ω → ℝ, ∑ i, h i = 0 →
      4 * Fintype.card Λ * γ * ∑ i, h i ^ 2 ≤ ∑ i, ∑ a, (h i - h (ρ a i)) ^ 2)
    (g : Ω → ℝ) :
    ∑ a, ∑ j, (g j + g (ρ a j) - (∑ j', (g j' + g (ρ a j'))) / Fintype.card Ω) ^ 2 ≤
      4 * Fintype.card Λ * (1 - γ) * ∑ j, (g j - (∑ j', g j') / Fintype.card Ω) ^ 2 := by sorry

end BinaryThreeLCC.JM
