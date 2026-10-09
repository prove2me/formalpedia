-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_theorem_2_9
-- name    : ErdosRenyiLSC.Main.theorem_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:52.823479+00:00
-- url     : https://prove2.me/theorems/4933cf3d-941b-42ab-b338-593e00ce0f3d
-- title:
--   Theorem 2.9 — local semicircle law for A
-- statement:
--   Let $H_N$ be the sparse real symmetric ensemble of Definition 2.1 and let $A_N=H_N+f_N|e_N\rangle\langle e_N|$ with $0\le f_N\le N^C$. Suppose $\xi_N\sim(A_0/2)\log\log N$ and $q_N\ge(\log N)^{C_1\xi_N}$. There are universal constants $C_1,C_2>0$ and a positive $\nu$ depending on the fixed model constants such that, with $(\xi,\nu)$-high probability, simultaneously for every $z=E+i\eta\in D$,
--
--   $$|\widetilde m(z)-m_{\mathrm{sc}}(z)|\le(\log N)^{C_2\xi}\left(\min\left\{\frac1{q^2\sqrt{\kappa_E+\eta}},\frac1q\right\}+\frac1{N\eta}\right).$$
--
--   Moreover, if $f_N\le C_0\sqrt N$ for a fixed $C_0>0$, then another event holds with $(\xi,\nu)$-high probability: simultaneously for every $z\in D$ and all $i,j$,
--
--   $$|\widetilde G_{ij}(z)-\delta_{ij}m_{\mathrm{sc}}(z)|\le(\log N)^{C_2\xi}\left(\frac1q+\sqrt{\frac{\operatorname{Im}m_{\mathrm{sc}}(z)}{N\eta}}+\frac1{N\eta}\right).$$
--
--   Together these bounds control the empirical spectral density and individual resolvent entries of the noncentered matrix down to the local spectral scale.
--
--   **Formalization Note** Both conclusions concern $A_N$, not the centered matrix $H_N$. The constant $C_0$ is chosen before $\nu$, and each intersection over spectral parameters lies inside one probability event. The matrix family and asymptotic hypotheses use one probability space and eventual conditions in $N$.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, pp. 9–10, Theorem 2.9 (2.20)–(2.22)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Theorem 2.9, pp. 9–10: both (2.20) and the conditional (2.22). -/
theorem theorem_2_9 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (A₀ Sigma C C₀ : ℝ), 10 ≤ A₀ → 3 ≤ Sigma → 0 < C → 0 < C₀ →
      ∃ ν : ℝ, 0 < ν ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
          (ξ q f : ℕ → ℝ) (a₀ : ℝ),
          0 < a₀ → IsSparseEnsemble P H ξ q a₀ A₀ C →
          (∀ᶠ N in (Filter.atTop : Filter ℕ),
            0 ≤ f N ∧ f N ≤ (N : ℝ) ^ C) →
          Filter.Tendsto
            (fun N : ℕ => ξ N / (A₀ / 2 * Real.log (Real.log (N : ℝ))))
            Filter.atTop (nhds 1) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ),
            q N ≥ Real.log (N : ℝ) ^ (C₁ * ξ N)) →
          HighProb P ξ ν (fun N =>
            {ω | ∀ z ∈ domD Sigma,
              ‖stieltjes (deformedMatrix H f N ω) z - msc z‖ ≤
                Real.log (N : ℝ) ^ (C₂ * ξ N) *
                  (min
                    (1 / (q N ^ 2 * Real.sqrt (kappa z.re + z.im)))
                    (1 / q N) + 1 / ((N : ℝ) * z.im))}) ∧
          ((∀ᶠ N in (Filter.atTop : Filter ℕ), f N ≤ C₀ * Real.sqrt (N : ℝ)) →
            HighProb P ξ ν (fun N =>
              {ω | ∀ z ∈ domD Sigma, ∀ i j : Fin N,
                ‖resolvent (deformedMatrix H f N ω) z i j -
                  (if i = j then msc z else 0)‖ ≤
                  Real.log (N : ℝ) ^ (C₂ * ξ N) *
                    (1 / q N +
                      Real.sqrt ((msc z).im / ((N : ℝ) * z.im)) +
                      1 / ((N : ℝ) * z.im))})) := by sorry

end ErdosRenyiLSC.Main
