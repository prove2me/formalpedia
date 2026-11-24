-- Prove2me | Theorems.Thm_BB6Kit_prop37_numeric
-- name    : BB6Kit.prop37_numeric
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-24T06:58:21.303427+00:00
-- url     : https://prove2.me/theorems/207af130-fa9b-4d33-ad2b-83750c85552c
-- title:
--   Final estimate of Prop. 3.7: combining (3.14)–(3.16) with Lemma 3.4
-- statement:
--   The closing numerical step of the proof of Proposition 3.7 of the Mignotte–Voutier kit.
--
--   **Theorem.** Under the hypotheses of `BB6Kit.prop37`, including $\rho\ge2$ and $\Lambda'<\rho^{-KL}$, let $B(\rho)$ be the right-hand side of `BB6Kit.prop37_max`. Then for every $\mathcal I$, $$(\Lambda')^{N-|\mathcal I|}\,\frac{B(\rho)}{\rho^{\Theta(K-1,|\mathcal I|)}}<\exp\Bigl(\rho\sum_jG_j\log\alpha_j+\log N!+\tfrac{N(K-1)}{3}\log b-\tfrac{N^2}{2K}\bigl(1-\tfrac{2}{3L}-\tfrac{2}{3KL}-\tfrac{1}{3L^2}-\tfrac{16}{3K^2L}\bigr)\log\rho+0.001\Bigr).$$
--
--   The proof combines six facts:
--
--   - (3.14): $\rho G_3|\Lambda|/b_3<0.001$;
--   - (3.15): $(\Lambda')^{N-|\mathcal I|}\le\rho^{-KL(N-|\mathcal I|)}$;
--   - Lemma 3.4 (via Lemma 3.3): $KL(N-I)+\Theta(K-1,I)\ge\tfrac{N^2}{2K}(1+\tfrac2L-\tfrac6{KL}-\tfrac1{3L^2})$;
--   - the counts $\sum k_i=\sum m_i=N(K-1)/3$, from (3.16);
--   - the identity $b^{N(K-1)/3}=(b_3'\eta_0)^{\sum k_i}(b_3''\zeta_0)^{\sum m_i}/\prod k_i!m_i!$, from (2.5);
--   - the source's bracket is weaker than the exact one, which leaves slack.
--
--   Checked numerically (all $0\le|\mathcal I|\le N$, with $\Theta$ computed exactly) on instances with $K=3,4,5$; the logarithmic margin is at least 14.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, proof of Proposition 3.7: (3.14), (3.15), (3.16), Lemmas 3.3 and 3.4, and (2.5).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi
import Definitions.Def_BB6Theta

namespace BB6Kit
theorem prop37_numeric (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ) (ρ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0) (hρ : 2 ≤ ρ)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst)
    (hsmall : BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) < ρ ^ (-((K : ℝ) * L))) :
    ∀ I : Finset (Fin N),
      BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ^ (N - I.card) *
        (((N.factorial : ℝ) * (∏ i, (((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) ^ (kml i).1 * ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) ^ (kml i).2.1 / (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)))) * (ρ * (((R : ℝ) - 1) / 2 + ((b1 / Nat.gcd b1 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) * (((T : ℝ) - 1) / 2))) ^ (∑ i, (kml i).1) * (ρ * (((S : ℝ) - 1) / 2 + ((b2 / Nat.gcd b2 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) * (((T : ℝ) - 1) / 2))) ^ (∑ i, (kml i).2.1) *
        Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
          BB6Kit.GK N L R S T T * (Real.log (α3 : ℝ) + |((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ))| / (b3 : ℝ))))) / ρ ^ BB6Theta.theta (K - 1) I.card) <
        Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) + BB6Kit.GK N L R S T T * Real.log (α3 : ℝ)) + Real.log (N.factorial : ℝ) +
        (N : ℝ) * ((K : ℝ) - 1) / 3 * Real.log (BB6Kit.bK K R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3)) -
        (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 - 2 / (3 * (L : ℝ)) - 2 / (3 * (K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2) -
          16 / (3 * (K : ℝ) ^ 2 * L)) * Real.log ρ + 0.001) := by
  sorry
end BB6Kit
