-- Prove2me | Theorems.Thm_ContJRP_Align_theorem_1_3_approximation
-- name    : ContJRP.Align.theorem_1_3_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:53:00.444768+00:00
-- url     : https://prove2.me/theorems/c4fa3b97-a717-4e9e-81d5-689f859c51a5
-- title:
--   Theorem 1.3, p. 5 — the easy policy is (1+2ϵ)-close and every Ψ-pairwise-alignment policy is (1+5ϵ)-close to any reference policy
-- statement:
--   Consider $n\ge1$ commodities with joint ordering cost $K_0>0$ and EOQ parameters $K_i,H_i>0$, and let $\epsilon\in(0,\tfrac12)$. Let $T^*$ be any policy with all $T^*_i>0$, and let $\widetilde{\mathrm{OPT}}$ satisfy $F(T^*)\le\widetilde{\mathrm{OPT}}\le2F(T^*)$.
--
--   **(a) Easy regime.** If $T^*_{\min}\ge\frac n\epsilon\cdot\frac{K_0}{\widetilde{\mathrm{OPT}}}$, the easy policy $\hat T_i=\sqrt{(K_0+K_i)/H_i}$ satisfies $F(\hat T)\le(1+2\epsilon)F(T^*)$.
--
--   **(b) Difficult regime.** If $T^*_{\min}<\frac n\epsilon\cdot\frac{K_0}{\widetilde{\mathrm{OPT}}}$, then
--
--   1. some power of $1+\epsilon/2$ times $K_0/\widetilde{\mathrm{OPT}}$, below $\frac n\epsilon\cdot\frac{K_0}{\widetilde{\mathrm{OPT}}}$, satisfies (2) as a guess $\tilde T_{\min}$;
--   2. for every $\tilde T_{\min}$ satisfying (2) and every choice of representatives $R^*$, (LP) has a feasible solution whose representatives in different components of $G^*_\Psi$ are misaligned; and for every such solution $\hat{\mathcal R}$ and every final policy $\hat T$ built from it,
--   $$F(\hat T)\le(1+5\epsilon)\cdot F(T^*)\qquad\text{and}\qquad K_0\lim_{\Delta\to\infty}\frac{N(\hat{\mathcal R},\Delta)}{\Delta}+\sum_{i\in[n]}C_i(\hat T_i)\le(1+5\epsilon)\cdot F(T^*).$$
--
--   Taking $T^*$ to be an optimal policy recovers the page's setting; this is the approximation guarantee of the Ψ-pairwise alignment scheme: $1+5\epsilon$, which becomes the paper's $1+\epsilon$ after rescaling $\epsilon$.
--
--   **Formalization Note** The running-time half of Theorem 1.3 is not formalized, and neither is the selection of the cheapest candidate among all guesses (§3.3). The constants are those the analysis proves, $1+2\epsilon$ (Lemma 2.1) and $1+5\epsilon$ ((3) and Lemma 3.6), with no rescaling of $\epsilon$. $T^*$ is an arbitrary positive policy rather than an optimal one; the page uses optimality only through the bracket on $\widetilde{\mathrm{OPT}}$. The second inequality in (b) bounds the cost of the joint orders the policy places at all multiples of $\hat{\mathcal R}$ (§2.6, step 1), which dominates $J(\hat T)$. Segments are 0-indexed in Lean.
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 5, Theorem 1.3; constants from p. 6 (Lemma 2.1), p. 7 (the grid for (2)), p. 12 (§3 intro, (3)) and p. 15 (Lemma 3.6)

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem theorem_1_3_approximation {n : ℕ} [NeZero n] (K0 : ℝ) (K H : Fin n → ℝ)
    (hK0 : 0 < K0) (hK : ∀ i, 0 < K i) (hH : ∀ i, 0 < H i)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (OPT : ℝ) (hOPT1 : totalCost K0 K H Tstar ≤ OPT) (hOPT2 : OPT ≤ 2 * totalCost K0 K H Tstar) :
    -- (a) the easy regime (Lemma 2.1)
    ((n : ℝ) / ε * (K0 / OPT) ≤ tmin Tstar →
      totalCost K0 K H (easyPolicy K0 K H) ≤ (1 + 2 * ε) * totalCost K0 K H Tstar) ∧
    -- (b) the difficult regime
    (tmin Tstar < (n : ℝ) / ε * (K0 / OPT) →
      -- the grid of powers of 1 + ε/2 in [K₀/OPT~, (n/ε)·K₀/OPT~) contains a guess satisfying (2)
      (∃ j : ℕ, (1 + ε / 2) ^ j * (K0 / OPT) < (n : ℝ) / ε * (K0 / OPT) ∧
        (1 - ε / 2) * tmin Tstar ≤ (1 + ε / 2) ^ j * (K0 / OPT) ∧
        (1 + ε / 2) ^ j * (K0 / OPT) ≤ tmin Tstar) ∧
      -- for every guess satisfying (2) and every choice of representatives:
      ∀ Tt : ℝ, (1 - ε / 2) * tmin Tstar ≤ Tt → Tt ≤ tmin Tstar →
        ∀ Rstar : ℕ → ℝ, IsRepChoice ε Tt Tstar Rstar →
          -- a cross-component misaligned feasible solution of (LP) exists (Lemma 2.5), and
          (∃ R : ℕ → ℝ, IsLPFeasible ε Tt Tstar Rstar R ∧ CrossMisaligned ε Tt Tstar Rstar R) ∧
          -- the final policy of every such solution is within 1 + 5ε of Tstar
          ∀ R : ℕ → ℝ, IsLPFeasible ε Tt Tstar Rstar R → CrossMisaligned ε Tt Tstar Rstar R →
            ∀ That : Fin n → ℝ, IsFinalPolicy K H ε Tt Tstar R That →
              totalCost K0 K H That ≤ (1 + 5 * ε) * totalCost K0 K H Tstar ∧
              K0 * orderDensity (active ε Tt Tstar) R + ∑ i, eoqCost (K i) (H i) (That i) ≤
                (1 + 5 * ε) * totalCost K0 K H Tstar) := by sorry

end ContJRP.Align
