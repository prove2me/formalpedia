-- Prove2me | Theorems.Thm_DQI_Semicircle_lemma_A_1
-- name    : DQI.Semicircle.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:27.495769+00:00
-- url     : https://prove2.me/theorems/f814f519-5470-4857-936a-d6943bbb805e
-- title:
--   Lemma A.1, p. 72 — if each x_j satisfies a x_j² + b x_j + c = 0 (a ≠ 0), then P(x_1 + … + x_m) = Σ_k u_k P^(k)(x_1, …, x_m)
-- statement:
--   Let $P$ be a real polynomial of degree $\ell$ in one variable, $m\ge0$, and $a,b,c\in\mathbb R$ with $a\neq0$. Then there are coefficients $u_0,u_1,\dots$ — depending only on $P,a,b,c,m$ — such that for all $x_1,\dots,x_m\in\mathbb R$ satisfying $a x_j^2+b x_j+c=0$ for every $j$,
--   $$P(x_1+\dots+x_m)=\sum_{k=0}^{\ell}u_k\,P^{(k)}(x_1,\dots,x_m),$$
--   where $P^{(k)}$ is the $k$-th elementary symmetric polynomial.
--
--   Applied to $g_i(\mathbf b_i\cdot\mathbf x)$, which all satisfy one quadratic identity, this writes every DQI state $|P(f)\rangle$ as a combination of the states $|P^{(k)}\rangle$, (44).
--
--   **Formalization Note** The coefficients are quantified before the variables ($\exists u\ \forall x$); with the order reversed the claim would be trivial since $P^{(0)}=1$.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 72, Appendix A, Lemma A.1

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- Lemma A.1, p. 72. The coefficients `u` are chosen before the variables `x`. -/
theorem lemma_A_1 (P : Polynomial ℝ) (a b c : ℝ) (ha : a ≠ 0) (m : ℕ) :
    ∃ u : ℕ → ℝ, ∀ x : Fin m → ℝ, (∀ j, a * x j ^ 2 + b * x j + c = 0) →
      P.eval (∑ j, x j) =
        ∑ k ∈ Finset.range (P.natDegree + 1), u k * (Finset.univ.val.map x).esymm k := by sorry

end DQI.Semicircle
