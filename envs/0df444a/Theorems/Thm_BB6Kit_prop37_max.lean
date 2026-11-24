-- Prove2me | Theorems.Thm_BB6Kit_prop37_max
-- name    : BB6Kit.prop37_max
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-24T06:59:12.063832+00:00
-- url     : https://prove2.me/theorems/1f54c181-5f28-4108-913a-d6b4fcd64310
-- title:
--   Bounds (3.12)–(3.13): $|\Psi_{\mathcal I}(x)|$ on the circle $|x|=\rho$
-- statement:
--   The upper bound (3.12)–(3.13) in the proof of Proposition 3.7 of the Mignotte–Voutier kit.
--
--   **Theorem.** Under the standing hypotheses of `BB6Kit.prop37_order`, let $\rho\ge0$. For every $\mathcal I$ and every complex $x$ with $|x|=\rho$, $$|\Psi_{\mathcal I}(x)|\le N!\prod_{i}\frac{b_3'^{k_i}b_3''^{m_i}}{k_i!\,m_i!}\,(\rho\eta_0)^{\sum k_i}(\rho\zeta_0)^{\sum m_i}\exp\Bigl(\rho\bigl(G_1\log\alpha_1+G_2\log\alpha_2+G_3(\log\alpha_3+|\Lambda|/b_3)\bigr)\Bigr).$$
--
--   The proof uses four facts:
--
--   - $|\theta_{i,j}|\le1$;
--   - $|\eta_j|\le\eta_0$ and $|\zeta_j|\le\zeta_0$;
--   - the permutation expansion of the determinant;
--   - the two-sided rearrangement bounds $|\sum_i\lambda_i\eta_{\sigma(i)}|\le G_1+\beta_1G_3$ and $|\sum_i\lambda_i\zeta_{\sigma(i)}|\le G_2+\beta_2G_3$ (Lemma 3.2, applied to $r$, $s$ and $t$).
--
--   Finally, $b_3\log\alpha_3=b_1\log\alpha_1+b_2\log\alpha_2-\Lambda$.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, proof of Proposition 3.7: the bound on |theta|, (3.12), (3.13), Lemma 3.2.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi
import Definitions.Def_BB6Theta

namespace BB6Kit
theorem prop37_max (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ) (ρ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst) (hρ : 0 ≤ ρ) :
    ∀ (I : Finset (Fin N)) (x : ℂ), ‖x‖ = ρ →
      ‖BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I x‖ ≤
      ((N.factorial : ℝ) * (∏ i, (((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) ^ (kml i).1 * ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) ^ (kml i).2.1 / (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)))) * (ρ * (((R : ℝ) - 1) / 2 + ((b1 / Nat.gcd b1 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) * (((T : ℝ) - 1) / 2))) ^ (∑ i, (kml i).1) * (ρ * (((S : ℝ) - 1) / 2 + ((b2 / Nat.gcd b2 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) * (((T : ℝ) - 1) / 2))) ^ (∑ i, (kml i).2.1) *
        Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
          BB6Kit.GK N L R S T T * (Real.log (α3 : ℝ) + |((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ))| / (b3 : ℝ))))) := by
  sorry
end BB6Kit
