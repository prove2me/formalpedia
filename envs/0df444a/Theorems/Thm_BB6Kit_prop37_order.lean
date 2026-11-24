-- Prove2me | Theorems.Thm_BB6Kit_prop37_order
-- name    : BB6Kit.prop37_order
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-24T06:58:33.702873+00:00
-- url     : https://prove2.me/theorems/acf5a22c-405a-4aeb-bf95-569b2849c611
-- title:
--   Lemma 3.6 for the kit: $\Psi_{\mathcal I}$ is entire and vanishes to order $\ge\Theta(K-1,|\mathcal I|)$ at $0$
-- statement:
--   Lemma 3.6 of the Mignotte–Voutier kit (Waldschmidt's Lemma 7.2 with $n=2$), specialised to the auxiliary determinants `BB6Psi.psi`.
--
--   **Theorem.** Let $K\ge3$, $L\ge5$, $N=K(K+1)L/2\le RST$, integers $\alpha_j>1$, $b_j>0$ with $\Lambda\ne0$. Let the rows enumerate $\{(k,m,\ell):k+m\le K-1,\ \ell<L\}$ and let the columns be distinct triples in the box. Then for every $\mathcal I\subseteq\{1,\dots,N\}$ the function $x\mapsto\Psi_{\mathcal I}(x)$ is entire, and $$\Psi_{\mathcal I}^{(n)}(0)=0\qquad\text{for all }n<\Theta(K-1,|\mathcal I|).$$
--
--   Here $\varphi_i(z_1,z_2)=p_i(z_1,z_2)\exp(\lambda_i(z_1\log\alpha_1+z_2\log\alpha_2))$, where $p_i$ is a monomial of total degree $k_i+m_i\le K-1$. The rows $i\notin\mathcal I$ are multiplied by the constants $\theta_{i,j}$. This gives the degree bound $K-1$ that the proof of Proposition 3.7 uses; the lemma as printed in the source says $K$. In the variables $w=z_1\log\alpha_1+z_2\log\alpha_2$ and $z_2$, each row expands into monomials $w^az_2^b$ with $b\le K-1$. By alternation, the coefficient of $x^n$ in the determinant vanishes unless the rows of $\mathcal I$ use $|\mathcal I|$ distinct monomials, of total degree at least $\Theta(K-1,|\mathcal I|)$ (see `BB6Theta.theta`).
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Lemma 3.6 and its use in the proof of Proposition 3.7; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups (Springer, 2000), Lemma 7.2.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi
import Definitions.Def_BB6Theta

namespace BB6Kit
theorem prop37_order (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst) :
    ∀ I : Finset (Fin N), Differentiable ℂ (fun x => BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I x) ∧
      ∀ n < BB6Theta.theta (K - 1) I.card, iteratedDeriv n (fun x => BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I x) 0 = 0 := by
  sorry
end BB6Kit
