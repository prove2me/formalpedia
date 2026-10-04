-- Prove2me | Theorems.Thm_EkelandVP_Constraints_lemma_3_3
-- name    : EkelandVP.Constraints.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:29:40.330673+00:00
-- url     : https://prove2.me/theorems/992449a6-516d-4fd6-91d1-716439a4066a
-- title:
--   Lemma 3.3, p. 331 — ε-Farkas–Minkowski lemma in V*: ‖w* − Σλᵢuᵢ* − Σμⱼvⱼ*‖* ≤ ε with μ ≥ 0
-- statement:
--   Let $V$ be a real Banach space with dual $V^*$ and dual norm $\|\cdot\|_*$, and let $\varepsilon>0$. Let $u_1^*,\dots,u_p^*$, $v_1^*,\dots,v_q^*$ and $w^*$ be continuous linear functionals on $V$ such that, for every $h\in V$,
--   $$\langle u_i^*,h\rangle=0\ (1\le i\le p)\ \text{ and }\ \langle v_j^*,h\rangle\ge0\ (1\le j\le q)\quad\Longrightarrow\quad\langle w^*,h\rangle\ge-\varepsilon\|h\|. \tag{3.19}$$
--   Then there are real numbers $\lambda_1,\dots,\lambda_p$ and nonnegative numbers $\mu_1,\dots,\mu_q$ such that
--   $$\Big\|w^*-\sum_{i=1}^p\lambda_iu_i^*-\sum_{j=1}^q\mu_jv_j^*\Big\|_*\le\varepsilon. \tag{3.20}$$
--
--   This is an approximate version of the Farkas–Minkowski lemma: a functional that is almost nonnegative on the cone cut out by finitely many linear constraints lies within $\varepsilon$ of the cone they generate in $V^*$.
--
--   **Formalization Note.** The page prints a strict inequality $<\varepsilon$ in (3.20). That is false: on $V=\mathbb R$ with $p=q=0$ and $w^*(h)=\varepsilon h$, (3.19) holds while $\|w^*\|_*=\varepsilon$. The page's proof separates $w^*$ from $\Gamma+\varepsilon B^*$ with $B^*$ the closed unit ball, which yields $\le\varepsilon$, and Theorem 3.1 uses $\le\varepsilon$; the Lean states $\le$. Functionals are `V →L[ℝ] ℝ` (the page applies the dual norm to them), and $\|\cdot\|_*$ is the operator norm. The hypothesis $\varepsilon>0$ is the section's standing $\varepsilon$.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 331, §3, Lemma 3.3, (3.19)–(3.20); proof pp. 332–333, (3.21)–(3.33)

import Mathlib

namespace EkelandVP.Constraints

/-- Ekeland (1974), Lemma 3.3, p. 331 (ε-Farkas–Minkowski lemma in `V*`): if the continuous linear
functionals `u_i`, `v_j`, `w` on the Banach space `V` are such that `⟨u_i, h⟩ = 0` for all `i` and
`⟨v_j, h⟩ ≥ 0` for all `j` imply `⟨w, h⟩ ≥ -ε ‖h‖` (3.19), then there are reals `λ_i` and nonnegative
reals `μ_j` with `‖w - Σ λ_i u_i - Σ μ_j v_j‖* ≤ ε` (3.20). The page prints `< ε` in (3.20); that is
false (take `V = ℝ`, no `u`, no `v`, `w = ε • id`), and the proof gives `≤ ε`. -/
theorem lemma_3_3 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (p q : ℕ) (u : Fin p → V →L[ℝ] ℝ) (v : Fin q → V →L[ℝ] ℝ) (w : V →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (h19 : ∀ h : V, (∀ i, u i h = 0) → (∀ j, 0 ≤ v j h) → -ε * ‖h‖ ≤ w h) :
    ∃ lam : Fin p → ℝ, ∃ mu : Fin q → ℝ, (∀ j, 0 ≤ mu j) ∧
      ‖w - ∑ i, lam i • u i - ∑ j, mu j • v j‖ ≤ ε := by sorry

end EkelandVP.Constraints
