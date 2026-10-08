-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_lemma_3_2_ii
-- name    : ConicQuadIPM.Complementarity.lemma_3_2_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:39.280234+00:00
-- url     : https://prove2.me/theorems/8f39351b-df9a-4122-bb95-2c41622e24da
-- title:
--   Lemma 3.2 ii), p. 11 — a point of N(1) satisfies XⁱSⁱeⁱ = µeⁱ for every i and τκ = µ
-- statement:
--   Let $K=K^1\times\dots\times K^k$ be as in §3 and let $(x,\tau,s,\kappa)\in\mathcal N(1)$, i.e. $(x;\tau),(s;\kappa)\in K\times\mathbb R_+$ and
--   $$
--   \min\Bigl(\sqrt{(x^1)^TQ^1x^1(s^1)^TQ^1s^1},\dots,\sqrt{(x^k)^TQ^kx^k(s^k)^TQ^ks^k},\ \tau\kappa\Bigr)\ge\mu=\frac{x^Ts+\tau\kappa}{k+1}.
--   $$
--   Then, with $X^i=\operatorname{mat}(T^ix^i)$ and $S^i=\operatorname{mat}(T^is^i)$,
--   $$
--   X^iS^ie^i=\mu e^i\quad(i=1,\dots,k)\qquad\text{and}\qquad \tau\kappa=\mu .
--   $$
--
--   So $\mathcal N(1)$ is the set of points that satisfy the relaxed complementarity conditions of the central path (21) exactly.
--
--   **Formalization Note.** The page writes "(x; τ), (s; κ) ∈ N(1)", a slip for $(x,\tau,s,\kappa)\in\mathcal N(1)$. The paper gives no proof. Block dimensions (`WellFormed`) are a disclosed hypothesis.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 11, Lemma 3.2 ii) (N(β) and µ defined on the same page)

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem lemma_3_2_ii {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x s : (i : Fin k) → Fin (n i) → ℝ) (τ κ : ℝ)
    (hN : Nbhd kind n 1 x τ s κ) :
    (∀ i : Fin k,
      (arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1 =
        mu x s τ κ • (e1 : Fin (n i) → ℝ)) ∧
    τ * κ = mu x s τ κ := by sorry

end ConicQuadIPM.Complementarity
