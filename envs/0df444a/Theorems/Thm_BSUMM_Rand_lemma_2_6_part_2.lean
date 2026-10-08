-- Prove2me | Theorems.Thm_BSUMM_Rand_lemma_2_6_part_2
-- name    : BSUMM.Rand.lemma_2_6_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:17.064826+00:00
-- url     : https://prove2.me/theorems/eae50daf-ff05-4a96-ac86-524f22d7b8cb
-- title:
--   Lemma 2.6(2) — E[Δ_p^{t+1} − Δ_p^t | z^t] ≤ p₀α^t‖Ex^t − q‖² − γ̂‖x̂^{t+1} − x^t‖² − α^t p₀(Ex^t − q)ᵀ(Ex̄^{t+1} − q)
-- statement:
--   Assume Assumptions A and B, and let $(p_0,\dots,p_K)$ be a probability vector with all $p_k>0$. There is a constant $\hat\gamma>0$, independent of the iterates, such that for RBSUM-M and each $t\ge1$, with the primal gap $\Delta_p^t=L(x^t;y^t)-d(y^t)$,
--
--   $$\mathbb E\big[\Delta_p^{t+1}-\Delta_p^t\,\big|\,z^t\big]\ \le\ p_0\alpha^t\|Ex^t-q\|^2-\hat\gamma\,\|\hat x^{t+1}-x^t\|^2-\alpha^tp_0\,(Ex^t-q)^\top(E\bar x^{t+1}-q), \tag{2.21}$$
--
--   for every $\bar x^{t+1}\in X(\hat y^{t+1})$, $\hat y^{t+1}=y^t+\alpha^t(q-Ex^t)$.
--
--   Together with Lemma 2.5 this gives the expected change of the combined primal-dual gap, the potential of the convergence proof.
--
--   **Formalization Note** The page prints $p_0\alpha^r$ and "independent of $y^r$"; the index $r$ belongs to the cyclic method, and the last line of the proof (p. 14) has $\alpha^tp_0\|Ex^t-q\|^2$, so the statement uses $\alpha^t$. "For some $\hat\gamma$" is stated as $\hat\gamma>0$, the constant of Lemma 2.3(2). The expectation is the one-step average over the random index at an arbitrary state $x\in X$, $y$, stepsize $a>0$, with $\hat x$ the block steps (2.5).
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 14, Lemma 2.6 (2.21)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- Lemma 2.6(2) (arXiv:1401.7079v1, p. 14, (2.21), with the printed `p_0 α^r` read as
`p_0 α^t`), in operator form: the one-step average of `Δ_p^{t+1} - Δ_p^t` is at most
`p_0 α^t ‖Ex^t - q‖² - γ̂ ‖x̂^{t+1} - x^t‖² - α^t p_0 (Ex^t - q)ᵀ(E x̄^{t+1} - q)` for every
`x̄^{t+1} ∈ X(ŷ^{t+1})`, with `γ̂ > 0` independent of the state. -/
theorem lemma_2_6_part_2 (S : Setting) (hA : S.AssumptionA) (u : S.UFun) (hB : S.AssumptionB u)
    (p : Fin (S.K + 1) → ℝ) (hp : S.IsProbVec p) :
    ∃ γhat : ℝ, 0 < γhat ∧
      ∀ x ∈ S.Xset, ∀ (y : S.Ysp) (a : ℝ) (xhat : S.Xsp), 0 < a → S.IsHatStep u x y xhat →
        ∀ xbar ∈ S.Xopt (S.dualStep x y a),
          S.condAvg p (fun x' y' => S.DeltaP x' y' - S.DeltaP x y) x y a xhat ≤
            p 0 * a * ‖S.Emap x - S.q‖ ^ 2 - γhat * ‖xhat - x‖ ^ 2 -
              a * p 0 * ⟪S.Emap x - S.q, S.Emap xbar - S.q⟫ := by sorry

end BSUMM.Rand
