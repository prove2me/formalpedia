-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_lemma_7_7
-- name    : ErdosRenyiLSC.Main.lemma_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:49.87472+00:00
-- url     : https://prove2.me/theorems/d2ada8bd-2d60-472b-ab6d-1f83a879171d
-- title:
--   Lemma 7.7, p. 71 — diagonal entries of G̃: (7.21) and (7.22) on Ω̃(η)
-- statement:
--   Let $A=H+f|e\rangle\langle e|$ satisfy Definition 2.2 (constants $A_0\ge10$, $C_m>0$) and assume (2.21), $0\le f\le C_0N^{1/2}$. Fix $\Sigma\ge3$ and let $L\ge8\xi$. Then there are constants $C,\nu>0$ such that for every $z=E+i\eta\in D_L$, on $\widetilde\Omega(\eta)$ with $(\xi,\nu)$-high probability,
--   $$\max_i|\widetilde G_{ii}(z)-\widetilde m(z)|\le C\,\Phi(z),$$
--   and, in particular, on $\widetilde\Omega(\eta)$ with $(\xi,\nu)$-high probability,
--   $$\widetilde\Lambda_d(z)\le\widetilde\Lambda(z)+C\,\Phi(z).$$
--   Here $\widetilde\Lambda=|\widetilde m-m_{\mathrm{sc}}|$, $\widetilde\Lambda_d=\max_i|\widetilde G_{ii}-m_{\mathrm{sc}}|$, and $\Phi$, $\widetilde\Omega(\eta)$ are as in Proposition 7.6.
--
--   The lemma reduces the diagonal entries of $\widetilde G$ to the normalized trace $\widetilde m$, which Lemma 7.1 compares with the trace for $H$.
--
--   **Formalization Note** "On $\widetilde\Omega(\eta)$ with high probability" means $\mathbb P(\widetilde\Omega(\eta)\cap\text{bad event})\le e^{-\nu(\log N)^\xi}$, for each fixed $z$ with one $N_0$ for all $z\in D_L$. $\nu$ is chosen before $a_0$ and the model; $C$ after $a_0$ and before the model (the paper's generic constants may depend on the constants of (2.4), p. 7).
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 71, Lemma 7.7, (7.21)–(7.22)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting
import Definitions.Def_ErdosRenyiLSC_Main_Resolvent

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Lemma 7.7, p. 71: assume (2.21). For `z = E + iη ∈ D_L`, on `Ω̃(η)` with
`(ξ, ν)`-high probability, (7.21) `max_i |G̃_ii(z) - m̃(z)| ≤ C Φ(z)` and
(7.22) `Λ̃_d(z) ≤ Λ̃(z) + C Φ(z)`, uniformly in `z ∈ D_L`. -/
theorem lemma_7_7 :
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
              ∀ i : Fin N,
                ‖resolvent (deformedMatrix H f N ω) z i i -
                    stieltjes (deformedMatrix H f N ω) z‖ ≤
                  C * Phi (ξ N) (q N) (deformedMatrix H f N ω) z}) ∧
          HighProbOnUnif P ξ ν (fun N => domDL Sigma L N)
            (fun N z => {ω | GoodAt Sigma L (ξ N) (deformedMatrix H f N ω) z.im})
            (fun N z => {ω |
              LamD (deformedMatrix H f N ω) z ≤
                Lam (deformedMatrix H f N ω) z +
                  C * Phi (ξ N) (q N) (deformedMatrix H f N ω) z}) := by sorry

end ErdosRenyiLSC.Main
