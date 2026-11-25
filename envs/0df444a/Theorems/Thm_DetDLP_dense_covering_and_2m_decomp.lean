-- Prove2me | Theorems.Thm_DetDLP_dense_covering_and_2m_decomp
-- name    : DetDLP.dense_covering_and_2m_decomp
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:49:51.225942+00:00
-- url     : https://prove2.me/theorems/ae5c7b0f-d9e8-4282-9cc2-162b21790be2
-- title:
--   Cauchy–Schwarz $7/8$-Covering and Universal $2m$-Term Decomposition from $\Phi(S) < 64/57$
-- statement:
--   In any finite abelian group $G$ (additive or multiplicative) with subsets $F_1, \dots, F_m \subseteq G$ and target mean $\mu > 0$, if the collision potential satisfies
--
--   $$\Phi(F) = \frac{|G| \cdot C_F + 64 (W_F - \mu)^2}{\mu^2} < \frac{64}{57},$$
--
--   then the $m$-fold sumset $D = F_1 + \dots + F_m$ satisfies $|D| \ge \frac{7}{8} |G|$, and consequently $D + D = G$: every element $X \in G$ admits a $2m$-term decomposition $X = \sum_{i=1}^m (A_i + B_i)$ with $A_i, B_i \in F_i$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.2, Proof of Theorem 3.1 (pp. 13–14)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

/-- Cauchy-Schwarz covering and universal 2m-term decomposition from the collision potential bound
`Φ(S) < 64 / 57` (Section 3.2 of the paper, both additive and multiplicative finite abelian groups). -/
theorem dense_covering_and_2m_decomp :
    (∀ {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {m : ℕ}
        (μ : ℝ) (F : Fin m → Finset G),
      0 < μ →
      collisionPotentialAdd μ F < (64 : ℝ) / 57 →
      7 * Fintype.card G ≤ 8 * (sumsetAdd F).card ∧
      ∀ X : G, ∃ A B : Fin m → G,
        (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
        (∑ i : Fin m, (A i + B i)) = X) ∧
    (∀ {G : Type} [CommGroup G] [Fintype G] [DecidableEq G] {m : ℕ}
        (μ : ℝ) (F : Fin m → Finset G),
      0 < μ →
      collisionPotentialMul μ F < (64 : ℝ) / 57 →
      7 * Fintype.card G ≤ 8 * (prodsetMul F).card ∧
      ∀ X : G, ∃ A B : Fin m → G,
        (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
        (∏ i : Fin m, (A i * B i)) = X) := by sorry

end DetDLP
