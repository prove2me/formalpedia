-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_theorem_3_1
-- name    : ErdosRenyiLSC.Main.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:37.63458+00:00
-- url     : https://prove2.me/theorems/2a2bb441-ff38-4dff-aded-4d0af131f8fa
-- title:
--   Theorem 3.1 — weak local semicircle law for H
-- statement:
--   Let $H_N$ satisfy Definition 2.1, and let $D_L$ be the domain where $|E|\le\Sigma$, $(\log N)^{L_N}/N\le\eta\le3$, with $L_N\ge8\xi_N$. There are positive constants $\nu$ and $C$ depending on the model constants such that each of the following events holds with $(\xi,\nu)$-high probability:
--
--   $$\bigcap_{z\in D_L}\left\{\max_{i\ne j}|G_{ij}(z)|\le \frac Cq+\frac{C(\log N)^{2\xi}}{\sqrt{N\eta}}\right\},$$
--
--   $$\bigcap_{z\in D_L}\left\{\max_i|G_{ii}(z)-m(z)|\le \frac{C(\log N)^\xi}{q}+\frac{C(\log N)^{2\xi}}{\sqrt{N\eta}}\right\},$$
--
--   $$\bigcap_{z\in D_L}\left\{|m(z)-m_{\mathrm{sc}}(z)|\le \frac{C(\log N)^\xi}{\sqrt q}+\frac{C(\log N)^{2\xi}}{(N\eta)^{1/3}}\right\}.$$
--
--   This is the preliminary local law for the centered matrix, including simultaneous control over the entire spectral domain.
--
--   **Formalization Note** The conditions on $H_N$, $\xi_N$, $q_N$, and $L_N$ are eventual in $N$, matching the asymptotic use of the result. Each displayed intersection is inside one probability event. $\nu$ is chosen before $a_0$ and the model (Remark 2.7: $\nu$ depends only on the constants of Definition 2.1 and $\Sigma$); $C$ is chosen after $a_0$ and before the model, since the paper's generic constants may depend on the constants of (2.4) (p. 7).
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 14, Theorem 3.1 (3.3)–(3.5)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Theorem 3.1, p. 14: all three bounds (3.3)–(3.5). -/
theorem theorem_3_1 :
    ∀ (A₀ Sigma Cmodel : ℝ), 10 ≤ A₀ → 3 ≤ Sigma → 0 < Cmodel →
      ∃ ν : ℝ, 0 < ν ∧ ∀ a₀ : ℝ, 0 < a₀ → ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
          (ξ q L : ℕ → ℝ),
          IsSparseEnsemble P H ξ q a₀ A₀ Cmodel →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), 8 * ξ N ≤ L N) →
          HighProb P ξ ν (fun N =>
            {ω | ∀ z ∈ domDL Sigma L N, ∀ i j : Fin N, i ≠ j →
              ‖resolvent (H N ω) z i j‖ ≤
                C / q N +
                  C * Real.log (N : ℝ) ^ (2 * ξ N) /
                    Real.sqrt ((N : ℝ) * z.im)}) ∧
          HighProb P ξ ν (fun N =>
            {ω | ∀ z ∈ domDL Sigma L N, ∀ i : Fin N,
              ‖resolvent (H N ω) z i i - stieltjes (H N ω) z‖ ≤
                C * Real.log (N : ℝ) ^ ξ N / q N +
                  C * Real.log (N : ℝ) ^ (2 * ξ N) /
                    Real.sqrt ((N : ℝ) * z.im)}) ∧
          HighProb P ξ ν (fun N =>
            {ω | ∀ z ∈ domDL Sigma L N,
              ‖stieltjes (H N ω) z - msc z‖ ≤
                C * Real.log (N : ℝ) ^ ξ N / Real.sqrt (q N) +
                  C * Real.log (N : ℝ) ^ (2 * ξ N) /
                    (((N : ℝ) * z.im) ^ ((1 : ℝ) / 3))}) := by sorry

end ErdosRenyiLSC.Main
