-- Prove2me | Theorems.Thm_BwSC_LowerBound_lemma_12
-- name    : BwSC.LowerBound.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:35:15.588981+00:00
-- url     : https://prove2.me/theorems/66f9b6a1-4417-42e2-bbc4-777ce0a946c9
-- title:
--   Lemma 12, p. 73 — Σ_{j∈[q+2]} Σ_k D_re(P′_{j,k}‖Q′_{j,k}) ≤ (K−r)/(8(q+2)); average ≤ (K−r)/(8(q+2)²K) ≤ q̄^(1)/4 (stopped records, q ≥ 1)
-- statement:
--   Let $K>1$, $T\ge2K$, $\pi\in\Pi_S$, $q=q(S,K)\ge1$, $r=r(S,K)$. With the reverse KL divergence $D_{\rm re}(\mathbb P\|\mathbb Q)=\mathrm{KL}(\mathbb Q\|\mathbb P)$ and the artificial measures $\mathbb P'_{j,k},\mathbb Q'_{j,k}$ (stopped at the first pull of arm $k$ in the window),
--   $$\sum_{j\in[q+2]}\sum_{k\in[K]}D_{\rm re}\big(\mathbb P'_{j,k}\,\|\,\mathbb Q'_{j,k}\big)\ \le\ \frac{K-r}{8(q+2)},$$
--   and, combined with Corollary 4 under $\mathbb Q$,
--   $$\frac1{(q+2)K}\sum_{j\in[q+2]}\sum_{k\in[K]}D_{\rm re}\big(\mathbb P'_{j,k}\,\|\,\mathbb Q'_{j,k}\big)\ \le\ \frac{K-r}{8(q+2)^2K}\ \le\ \frac{\overline{q^{(1)}}}{4}.$$
--
--   This is the divergence bound fed into the reverse Fano inequality in (46).
--
--   **Formalization Note** Divergences are in $[0,\infty]$ (Mathlib `klDiv`), so the first two bounds are stated in $[0,\infty]$. **Repair:** the printed measures (45) hide arm $k$'s rewards in the window but keep the actions there; a one-switch policy that keeps arm $k$ iff its first reward is positive already has $D_{\rm re}\ge0.31$ for $j=1$, where the page claims $0$. The records here stop at the first pull of $k$ in the window, which gives the divergence $\frac{(\Delta^{(1)}_j)^2}{2}\mathbb E_{\mathbf 0}[N_k(lo-1)]$ computed on p. 72 and keeps every constant. $q\ge1$ is assumed because $\Delta^{(1)}_{q+2}$ is undefined at $q=0$.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 73, Lemma 12; artificial measures pp. 71–72, (45)

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Lemma 12, p. 73 (for the artificial measures stopped at the first pull of arm `k` in the
window): `Σ_{j ∈ [q+2]} Σ_{k ∈ [K]} D_re(P'_{j,k} ∥ Q'_{j,k}) ≤ (K - r(S,K))/(8(q(S,K)+2))`, where
`D_re(P ∥ Q) = KL(Q ∥ P)`; combined with Corollary 4, the average is at most
`(K - r)/(8(q+2)²K) ≤ q̄^{(1)}/4`. Stated for `q(S,K) ≥ 1`. -/
theorem lemma_12 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (hq : 1 ≤ qIdx S K) :
    ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K, klDiv (artQ1 π S T j k) (artP1 π S T j k) ≤
        ENNReal.ofReal (((K : ℝ) - (rIdx S K : ℝ)) / (8 * ((qIdx S K : ℝ) + 2))) ∧
    ENNReal.ofReal (1 / (((qIdx S K : ℝ) + 2) * K)) *
        ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
          klDiv (artQ1 π S T j k) (artP1 π S T j k) ≤
        ENNReal.ofReal (((K : ℝ) - (rIdx S K : ℝ)) / (8 * ((qIdx S K : ℝ) + 2) ^ 2 * K)) ∧
    ((K : ℝ) - (rIdx S K : ℝ)) / (8 * ((qIdx S K : ℝ) + 2) ^ 2 * K) ≤
      qbar1 π S T / 4 := by sorry

end BwSC.LowerBound
