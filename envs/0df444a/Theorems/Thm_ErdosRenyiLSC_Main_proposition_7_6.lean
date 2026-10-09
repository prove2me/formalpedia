-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_proposition_7_6
-- name    : ErdosRenyiLSC.Main.proposition_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:37.378409+00:00
-- url     : https://prove2.me/theorems/f043a2cd-66b9-4012-9276-cc9b7a9482fb
-- title:
--   Proposition 7.6 (7.14), p. 69 — off-diagonal bound Λ̃_o ≤ CΦ on Ω̃(η)
-- statement:
--   Let $A=H+f|e\rangle\langle e|$ satisfy Definition 2.2 (constants $A_0\ge10$, $C_m>0$) and assume (2.21), $0\le f\le C_0N^{1/2}$. Fix $\Sigma\ge3$ and let $L\ge8\xi$. Then there are constants $C,\nu>0$ such that for every $z=E+i\eta\in D_L$
--   $$\widetilde\Lambda_o(z)=\max_{i\ne j}|\widetilde G_{ij}(z)|\le C\,\Phi(z)\qquad\text{in }\widetilde\Omega(\eta)\text{ with }(\xi,\nu)\text{-high probability},$$
--   that is, $\mathbb P\bigl(\widetilde\Omega(\eta)\cap\{\widetilde\Lambda_o(z)>C\Phi(z)\}\bigr)\le e^{-\nu(\log N)^\xi}$ for $N\ge N_0$, where $\Phi(z)=(\log N)^\xi/q+(\log N)^{2\xi}\bigl(\sqrt{\operatorname{Im}\widetilde m(z)/(N\eta)}+1/(N\eta)\bigr)$ and $\widetilde\Omega(\eta)$ is the event $\sup_{z'\in D_L,\ \operatorname{Im}z'=\eta}(\widetilde\Lambda_d+\widetilde\Lambda_o)(z')\le(\log N)^{-\xi}$.
--
--   Together with Lemma 7.7 this controls all matrix entries of $\widetilde G$ by the trace error, which is the bootstrapping step towards (2.22).
--
--   **Formalization Note** Only (7.14) is formalized; (7.15)–(7.16) involve the partial expectation of the noncentered entries. The bound is for each fixed $z$, with one $N_0$ for all $z\in D_L$. $\nu$ is chosen before $a_0$ and the model; $C$ after $a_0$ and before the model (the paper's generic constants may depend on the constants of (2.4), p. 7).
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 69, Proposition 7.6, (7.14), with (7.13) and Definition 7.3 (7.4), p. 66

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting
import Definitions.Def_ErdosRenyiLSC_Main_Resolvent

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Proposition 7.6, (7.14), p. 69: assume (2.21). For `z = E + iη ∈ D_L`,
`Λ̃_o(z) ≤ C Φ(z)` in `Ω̃(η)` with `(ξ, ν)`-high probability, i.e.
`P(Ω̃(η) ∩ {Λ̃_o(z) > C Φ(z)}) ≤ exp(-ν (log N)^ξ)`, uniformly in `z ∈ D_L`. -/
theorem proposition_7_6 :
    ∀ (A₀ Sigma Cm C₀ : ℝ), 10 ≤ A₀ → 3 ≤ Sigma → 0 < Cm → 0 < C₀ →
      ∃ ν : ℝ, 0 < ν ∧ ∀ a₀ : ℝ, 0 < a₀ → ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
          (ξ q f L : ℕ → ℝ),
          IsSparseEnsemble P H ξ q a₀ A₀ Cm →
          (∀ᶠ N in (Filter.atTop : Filter ℕ),
            0 ≤ f N ∧ f N ≤ (N : ℝ) ^ Cm) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), f N ≤ C₀ * Real.sqrt (N : ℝ)) →
          (∀ᶠ N in (Filter.atTop : Filter ℕ), 8 * ξ N ≤ L N) →
          HighProbOnUnif P ξ ν (fun N => domDL Sigma L N)
            (fun N z => {ω | GoodAt Sigma L (ξ N) (deformedMatrix H f N ω) z.im})
            (fun N z => {ω |
              LamO (deformedMatrix H f N ω) z ≤
                C * Phi (ξ N) (q N) (deformedMatrix H f N ω) z}) := by sorry

end ErdosRenyiLSC.Main
