-- Prove2me | Theorems.Thm_BB6Kit_prop37_term
-- name    : BB6Kit.prop37_term
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-24T06:34:33.390976+00:00
-- url     : https://prove2.me/theorems/2f2b12a8-3822-4332-b81c-ea490152cff4
-- title:
--   Per-term analytic bound in Prop. 3.7: $(\Lambda')^{N-|\mathcal I|}|\Psi_{\mathcal I}(1)|<\exp(E)$
-- statement:
--   The analytic heart of Proposition 3.7 of the Mignotte–Voutier kit: steps (3.11)–(3.16), applied to one term of the expansion (3.10).
--
--   **Theorem.** Under the hypotheses of `BB6Kit.prop37`, including $\rho\ge2$ and $\Lambda'<\rho^{-KL}$, every $\mathcal I\subseteq\{1,\dots,N\}$ satisfies $$(\Lambda')^{N-|\mathcal I|}\,|\Psi_{\mathcal I}(1)|<\exp\Bigl(\rho\sum_j G_j\log\alpha_j+\log N!+\tfrac{N(K-1)}{3}\log b-\tfrac{N^2}{2K}\bigl(1-\tfrac{2}{3L}-\tfrac{2}{3KL}-\tfrac{1}{3L^2}-\tfrac{16}{3K^2L}\bigr)\log\rho+0.001\Bigr).$$
--
--   The source argument has five steps:
--
--   1. Schwarz's lemma (3.11) gives $|\Psi_{\mathcal I}(1)|\le\rho^{-J}\max_{|x|=\rho}|\Psi_{\mathcal I}(x)|$, where $J\ge\Theta(K-1,|\mathcal I|)$ is the order of vanishing at $x=0$ (Lemma 3.6, from Waldschmidt's Lemma 7.2).
--   2. Expanding over permutations with $|\theta_{i,j}|\le1$, and applying Lemma 3.2, gives (3.12)–(3.13).
--   3. (3.14) gives $\rho G_3|\Lambda|/b_3<0.001$.
--   4. (3.15) gives $(\Lambda')^{N-|\mathcal I|}\rho^{-J}\le\rho^{-KL(N-|\mathcal I|)-J}$, and Lemma 3.4 bounds $KL(N-I)+\Theta(K-1,I)$ from below.
--   5. (3.16) and (2.5) give the factor $b^{N(K-1)/3}$.
--
--   Summing over the $2^N$ subsets gives Proposition 3.7: `BB6Kit.prop37` follows from this and `BB6Kit.prop37_expand`.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Section 3.3, proof of Proposition 3.7, eqs. (3.11)-(3.16), with Lemmas 3.2, 3.4, 3.6 and Schwarz's lemma (Waldschmidt, Diophantine approximation on linear algebraic groups, Lemma 2.3 p. 37 and Lemma 7.2).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi

namespace BB6Kit
theorem prop37_term (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ) (ρ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0) (hρ : 2 ≤ ρ)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst)
    (hsmall : BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) < ρ ^ (-((K : ℝ) * L))) :
    ∀ I : Finset (Fin N),
      BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ^ (N - I.card) * ‖BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I 1‖ <
        Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) + BB6Kit.GK N L R S T T * Real.log (α3 : ℝ)) + Real.log (N.factorial : ℝ) +
        (N : ℝ) * ((K : ℝ) - 1) / 3 * Real.log (BB6Kit.bK K R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3)) -
        (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 - 2 / (3 * (L : ℝ)) - 2 / (3 * (K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2) -
          16 / (3 * (K : ℝ) ^ 2 * L)) * Real.log ρ + 0.001) := by
  sorry
end BB6Kit
