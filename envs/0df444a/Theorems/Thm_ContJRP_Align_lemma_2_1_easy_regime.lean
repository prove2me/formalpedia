-- Prove2me | Theorems.Thm_ContJRP_Align_lemma_2_1_easy_regime
-- name    : ContJRP.Align.lemma_2_1_easy_regime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:41.174166+00:00
-- url     : https://prove2.me/theorems/8c80736b-288b-4af8-ae6f-43d8ea16ea1b
-- title:
--   Lemma 2.1, p. 6 — when T*_min ≥ (n/ϵ)K₀/OPT~, F(T̂) ≤ Σ C⁺_i(T̂_i) ≤ (1 + 2ϵ)F(T*)
-- statement:
--   Consider $n\ge1$ commodities with $K_0>0$ and $K_i,H_i>0$, a policy $T^*$ with all $T^*_i>0$, and an estimate $\widetilde{\mathrm{OPT}}$ with $F(T^*)\le\widetilde{\mathrm{OPT}}\le2F(T^*)$. Let $\epsilon\in(0,\tfrac12)$, $C^+_i(T)=(K_0+K_i)/T+H_iT$, and let $\hat T_i=\sqrt{(K_0+K_i)/H_i}$ be the easy policy. If
--   $$T^*_{\min}\ge\frac n\epsilon\cdot\frac{K_0}{\widetilde{\mathrm{OPT}}},$$
--   then
--   $$F(\hat T)\le\sum_{i\in[n]}C^+_i(\hat T_i)\le(1+2\epsilon)\cdot F(T^*).$$
--
--   This is the guarantee of the easy regime, and part (a) of Theorem 1.3.
--
--   **Formalization Note** $T^*$ is any policy with positive intervals satisfying the bracket on $\widetilde{\mathrm{OPT}}$; the page fixes an optimal one, but uses optimality only through this bracket. Positivity of $K_0,K_i,H_i$ and $n\ge1$ are readings of §1.1.
-- source:
--   Segev, The Continuous-Time Joint Replenishment Problem: ϵ-Optimal Policies via Pairwise Alignment, arXiv:2302.09941v1, p. 6, Lemma 2.1 (proof in §4.2, p. 18)

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy

namespace ContJRP.Align

theorem lemma_2_1_easy_regime {n : ℕ} [NeZero n] (K0 : ℝ) (K H : Fin n → ℝ) (hK0 : 0 < K0)
    (hK : ∀ i, 0 < K i) (hH : ∀ i, 0 < H i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (OPT : ℝ) (hOPT1 : totalCost K0 K H Tstar ≤ OPT) (hOPT2 : OPT ≤ 2 * totalCost K0 K H Tstar)
    (heasy : (n : ℝ) / ε * (K0 / OPT) ≤ tmin Tstar) :
    totalCost K0 K H (easyPolicy K0 K H) ≤
        ∑ i, eoqCost (K0 + K i) (H i) (easyPolicy K0 K H i) ∧
      ∑ i, eoqCost (K0 + K i) (H i) (easyPolicy K0 K H i) ≤
        (1 + 2 * ε) * totalCost K0 K H Tstar := by sorry

end ContJRP.Align
