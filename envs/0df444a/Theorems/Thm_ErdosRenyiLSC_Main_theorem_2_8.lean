-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_theorem_2_8
-- name    : ErdosRenyiLSC.Main.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:45.345742+00:00
-- url     : https://prove2.me/theorems/fdcc83e0-70b7-4747-aa83-3ecdcd7c3f88
-- title:
--   Theorem 2.8 — strong local semicircle law for H
-- statement:
--   For a centered sparse symmetric ensemble $H_N$ satisfying Definition 2.1, suppose $\xi_N\sim(A_0/2)\log\log N$ and $q_N\ge(\log N)^{C_1\xi_N}$. There are universal positive constants $C_1,C_2$ and a positive $\nu$ depending on the fixed model constants such that, with $(\xi,\nu)$-high probability, simultaneously for all $z=E+i\eta\in D$,
--
--   $$|m(z)-m_{\mathrm{sc}}(z)|\le(\log N)^{C_2\xi}\left(\min\left\{\frac1{q^2\sqrt{\kappa_E+\eta}},\frac1q\right\}+\frac1{N\eta}\right),$$
--
--   and, as a second high-probability event,
--
--   $$\max_{i,j}|G_{ij}(z)-\delta_{ij}m_{\mathrm{sc}}(z)|\le(\log N)^{C_2\xi}\left(\frac1q+\sqrt{\frac{\operatorname{Im}m_{\mathrm{sc}}(z)}{N\eta}}+\frac1{N\eta}\right).$$
--
--   This centered-matrix law is the principal input for the trace estimate for the noncentered matrix $A_N$.
--
--   **Formalization Note** The constants $C_1,C_2$ precede every model parameter, while $\nu$ precedes the random ensemble. Each estimate is simultaneous in $z$ inside its event.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 8, Theorem 2.8 (2.15)–(2.17)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Theorem 2.8, p. 8: the strong local semicircle law for the centered matrix. -/
theorem theorem_2_8 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (A₀ Sigma C : ℝ), 10 ≤ A₀ → 3 ≤ Sigma → 0 < C →
      ∃ ν : ℝ, 0 < ν ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
          (ξ q : ℕ → ℝ) (a₀ : ℝ),
          0 < a₀ → IsSparseEnsemble P H ξ q a₀ A₀ C →
          Filter.Tendsto
            (fun N : ℕ => ξ N / (A₀ / 2 * Real.log (Real.log (N : ℝ))))
            Filter.atTop (nhds 1) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ),
            q N ≥ Real.log (N : ℝ) ^ (C₁ * ξ N)) →
          HighProb P ξ ν (fun N =>
            {ω | ∀ z ∈ domD Sigma,
              ‖stieltjes (H N ω) z - msc z‖ ≤
                Real.log (N : ℝ) ^ (C₂ * ξ N) *
                  (min
                    (1 / (q N ^ 2 * Real.sqrt (kappa z.re + z.im)))
                    (1 / q N) + 1 / ((N : ℝ) * z.im))}) ∧
          HighProb P ξ ν (fun N =>
            {ω | ∀ z ∈ domD Sigma, ∀ i j : Fin N,
              ‖resolvent (H N ω) z i j -
                (if i = j then msc z else 0)‖ ≤
                Real.log (N : ℝ) ^ (C₂ * ξ N) *
                  (1 / q N +
                    Real.sqrt ((msc z).im / ((N : ℝ) * z.im)) +
                    1 / ((N : ℝ) * z.im))}) := by sorry

end ErdosRenyiLSC.Main
