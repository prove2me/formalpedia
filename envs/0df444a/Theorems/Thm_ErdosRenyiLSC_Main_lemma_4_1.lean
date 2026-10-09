-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_lemma_4_1
-- name    : ErdosRenyiLSC.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:40.739351+00:00
-- url     : https://prove2.me/theorems/678a30d7-7ce6-479b-9f5c-fca8b21aef00
-- title:
--   Lemma 4.1, p. 29 — fluctuation averaging bound (4.2) for [Z]
-- statement:
--   Let $H$ satisfy Definition 2.1 with parameters $\xi$, $q$ and constants $A_0\ge10$, $C>0$, and fix $\Sigma\ge3$ and $\nu>0$. Suppose that $q\ge(\log N)^{5\xi}$, that $L\ge14\xi$, that $\widetilde D\subset D_L$, and that $\gamma$ is a deterministic function with $\gamma(z)\le(\log N)^{-\xi}$ on $\widetilde D$ such that, for each $z\in\widetilde D$, $\Lambda(z)=|m(z)-m_{\mathrm{sc}}(z)|\le\gamma(z)$ with $(\xi,\nu)$-high probability. Then there is $\nu'>0$, depending only on $\nu$, $A_0$, $\Sigma$, $C$, such that for each $z=E+i\eta\in\widetilde D$, with $(\xi-2,\nu')$-high probability,
--   $$\bigl|[Z](z)\bigr|\le(\log N)^{14\xi}\Bigl(\frac1{q^2}+\frac1{(N\eta)^2}+(\log N)^{4\xi}\frac{\operatorname{Im}m_{\mathrm{sc}}(z)+\gamma(z)}{N\eta}\Bigr),$$
--   where $[Z]=N^{-1}\sum_iZ_i$ and $Z_i=\sum^{(i)}_{k,l}(h_{ik}h_{li}-N^{-1}\delta_{kl})G^{(i)}_{kl}$.
--
--   The average $[Z]$ is much smaller than a typical $Z_i$; this gain drives the iteration that improves the weak local law to the strong one.
--
--   **Formalization Note** "With high probability for $z\in\widetilde D$" is read for each fixed $z$, uniformly in $z$: one $N_0$ serves all $z\in\widetilde D$, both in the hypothesis and in the conclusion. As allowed by Remark 2.7, the conclusion's $\nu'$ may be smaller than $\nu$. $\widetilde D$, $\gamma$ and $L$ may depend on $N$; all conditions hold for sufficiently large $N$. The consequence (4.3) is not part of this statement.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 29, Lemma 4.1, (4.1)–(4.2)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting
import Definitions.Def_ErdosRenyiLSC_Main_Resolvent

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Lemma 4.1, p. 29, (4.2): fluctuation averaging. If `q ≥ (log N)^{5ξ}`, `D̃ ⊂ D_L` with
`L ≥ 14ξ`, and `Λ(z) ≤ γ(z)` holds with `(ξ, ν)`-high probability for `z ∈ D̃`, where `γ` is
deterministic with `γ ≤ (log N)^{-ξ}`, then with `(ξ - 2, ν)`-high probability
`|[Z](z)| ≤ (log N)^{14ξ} (q^{-2} + (Nη)^{-2} + (log N)^{4ξ} (Im m_sc(z) + γ(z)) / (Nη))`
for `z ∈ D̃`. Both high-probability statements are for each fixed `z`, uniformly in `z ∈ D̃`;
by Remark 2.7 the conclusion's `ν` may be smaller than the hypothesis's. -/
theorem lemma_4_1 :
    ∀ (A₀ Sigma C : ℝ), 10 ≤ A₀ → 3 ≤ Sigma → 0 < C →
    ∀ ν : ℝ, 0 < ν →
      ∃ ν' : ℝ, 0 < ν' ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
          (ξ q L : ℕ → ℝ) (a₀ : ℝ) (Dt : ℕ → Set ℂ) (γ : ℕ → ℂ → ℝ),
          0 < a₀ → IsSparseEnsemble P H ξ q a₀ A₀ C →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), q N ≥ Real.log (N : ℝ) ^ (5 * ξ N)) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), 14 * ξ N ≤ L N) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), Dt N ⊆ domDL Sigma L N) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ z ∈ Dt N,
            γ N z ≤ Real.log (N : ℝ) ^ (-ξ N)) →
          HighProbUnif P ξ ν Dt (fun N z => {ω | Lam (H N ω) z ≤ γ N z}) →
          HighProbUnif P (fun N => ξ N - 2) ν' Dt (fun N z =>
            {ω | ‖Zavg (H N ω) z‖ ≤
              Real.log (N : ℝ) ^ (14 * ξ N) *
                (1 / q N ^ 2 + 1 / ((N : ℝ) * z.im) ^ 2 +
                  Real.log (N : ℝ) ^ (4 * ξ N) *
                    (((msc z).im + γ N z) / ((N : ℝ) * z.im)))}) := by sorry

end ErdosRenyiLSC.Main
