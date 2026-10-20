-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_proposition_1_allocation
-- name    : CryptoMembership.PerfectInfo.proposition_1_allocation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:47.148977+00:00
-- url     : https://prove2.me/theorems/cfb8e4a0-5e56-4ef9-a8b9-2bf97ab36f00
-- title:
--   Proposition 1, p. 14 (PDF 15) and A.1 — pairwise equilibrium allocation C_i(i) = (1 − η_c)e^{A_i}, C_j(i) = η_c e^{A_j}, utility e^{(1−η_c)A_i+η_cA_j}
-- statement:
--   Let $\eta_c\in(0,1)$ and let two matched households $i$ and $j$ own $e^{A_i}$ units of good $i$ and $e^{A_j}$ units of good $j$, with Cobb–Douglas utility $U(C_i,C_j)=(C_i/(1-\eta_c))^{1-\eta_c}(C_j/\eta_c)^{\eta_c}$ over own and partner's good.
--
--   1. In every pairwise competitive equilibrium (positive prices $p_i,p_j$, each household maximizing $U$ on its budget line $p_iC_i+p_jC_j=p_ie^{A_i}$, both goods markets clearing) the allocation is
--   $$C_i(i)=(1-\eta_c)e^{A_i},\quad C_j(i)=\eta_ce^{A_j},\quad C_j(j)=(1-\eta_c)e^{A_j},\quad C_i(j)=\eta_ce^{A_i},$$
--   and the relative price is $p_i/p_j=e^{A_j-A_i}$.
--   2. Conversely, for every $p_j>0$ this allocation with $p_i=p_je^{A_j-A_i}$ is a pairwise competitive equilibrium.
--   3. The realized utility is $U(C_i(i),C_j(i))=e^{(1-\eta_c)A_i+\eta_cA_j}$.
--   4. The marginal-utility price of (10) is $\frac{1-\eta_c}{C_i(i)}U(C_i(i),C_j(i))=e^{\eta_c(A_j-A_i)}$, and $U(C_i(i),C_j(i))=e^{\eta_c(A_j-A_i)}e^{A_i}=p_ie^{A_i}$.
--
--   This is the $t=2$ part of Proposition 1; it justifies the realized match utility used at $t=1$.
--
--   **Formalization Note** The page calls $p_i=e^{\eta_c(A_j-A_i)}$ "the price of its produced good". Applying the same formula to household $j$ gives $p_i/p_j=e^{2\eta_c(A_j-A_i)}$, which supports the allocation only when $\eta_c=1/2$ or $A_i=A_j$. The statement therefore records the equilibrium relative price $e^{A_j-A_i}$ and states $p_i$ only as the marginal-utility expression (10) with the Lagrange multiplier normalized to 1, as in the proof.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), p. 14 (PDF 15), Proposition 1; A.1, pp. 30–31 (PDF 31–32), eq. (10)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

theorem proposition_1_allocation (eta Ai Aj : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (∀ pi pj cii cij cjj cji : ℝ, IsPairEquilibrium eta Ai Aj pi pj cii cij cjj cji →
      cii = (1 - eta) * Real.exp Ai ∧ cij = eta * Real.exp Aj ∧
      cjj = (1 - eta) * Real.exp Aj ∧ cji = eta * Real.exp Ai ∧
      pi / pj = Real.exp (Aj - Ai)) ∧
    (∀ pj : ℝ, 0 < pj →
      IsPairEquilibrium eta Ai Aj (pj * Real.exp (Aj - Ai)) pj
        ((1 - eta) * Real.exp Ai) (eta * Real.exp Aj) ((1 - eta) * Real.exp Aj) (eta * Real.exp Ai)) ∧
    U eta ((1 - eta) * Real.exp Ai) (eta * Real.exp Aj) = matchUtility eta Ai Aj ∧
    (1 - eta) / ((1 - eta) * Real.exp Ai) * U eta ((1 - eta) * Real.exp Ai) (eta * Real.exp Aj) =
      Real.exp (eta * (Aj - Ai)) ∧
    U eta ((1 - eta) * Real.exp Ai) (eta * Real.exp Aj) =
      Real.exp (eta * (Aj - Ai)) * Real.exp Ai := by sorry

end CryptoMembership.PerfectInfo
