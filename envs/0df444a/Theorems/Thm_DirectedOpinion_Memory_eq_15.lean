-- Prove2me | Theorems.Thm_DirectedOpinion_Memory_eq_15
-- name    : DirectedOpinion.Memory.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:57.234717+00:00
-- url     : https://prove2.me/theorems/f5268631-da91-47db-a6f5-e107fe500055
-- title:
--   (15) — variance of the root opinion of the no-memory recursion (9): d²Var(𝓩_∅)/(c+d)² + ρ*₂d²Var(𝓩₁)/((c+d)²((c+d)² − ρ₂))
-- statement:
--   On a delayed marked Galton–Watson tree with the Section 5.1 signals $\mathcal W$, consider the no-memory recursion (9),
--   $$\mathcal R_{\mathbf i}^{(k+1)}=\sum_{j=1}^{\mathcal N_{\mathbf i}}\frac{\mathcal C_{(\mathbf i,j)}}{c+d}\mathcal R_{(\mathbf i,j)}^{(k)}+\frac{\mathcal W_{\mathbf i}^{(k)}}{c+d},$$
--   and let $\mathcal R^*$ be its limiting root opinion. If $c,d>0$, $c+d<1$ and $P(\mathcal N_\varnothing>0)=P(\mathcal N_1>0)=1$, then
--   $$\mathrm{Var}(\mathcal R^*)=\frac{d^2}{(c+d)^2}\mathrm{Var}(\mathcal Z_\varnothing)+\frac{\rho_2^*d^2}{(c+d)^2((c+d)^2-\rho_2)}\mathrm{Var}(\mathcal Z_1),$$
--   where $\rho_2^*=E[\sum_{i=1}^{\mathcal N_\varnothing}\mathcal C_i^2]$ and $\rho_2=E[\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)}^2]$.
--
--   This is the right-hand side of the comparison in Proposition 6.
--
--   **Formalization Note.** The paper says this "was shown in Proposition 4"; it is Proposition 4 applied to recursion (9), i.e. with weights $\mathcal C/(c+d)$ (summing to $c/(c+d)$), signals $\mathcal W/(c+d)=\frac{d}{c+d}\mathcal Z$ a.s., and hence $\rho_2/(c+d)^2$ and $\rho_2^*/(c+d)^2$ in place of $\rho_2$, $\rho_2^*$. It is stated directly on the limit tree under the Section 5 standing assumptions, without the graph sequence of Theorem 2. The root opinion of (9) is `RstarNoMem`: the series $\sum_s(\Delta^s\mathcal W^{(s)}/(c+d))(\varnothing)$ with $\Delta$ of weights $\mathcal C/(c+d)$ and no self term, absolutely summable since the weights sum to $c/(c+d)<1$. The hypotheses $0<c$, $c+d<1$ are those of Proposition 6, where (15) appears.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 31, proof of Proposition 6, (15)

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting

namespace DirectedOpinion.Memory
open MeasureTheory ProbabilityTheory

/-- (15), p. 31: the variance of the root opinion 𝓡* of the no-memory recursion (9),
Var(𝓡*) = d²/(c+d)² Var(𝓩_∅) + ρ*₂d²/((c+d)²((c+d)² − ρ₂)) Var(𝓩₁). -/
theorem eq_15 {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : DirectedOpinion.NoMemory.MarkFns M) (X : DirectedOpinion.NoMemory.Label → Ω → M)
    (U : DirectedOpinion.NoMemory.Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hGW : DirectedOpinion.NoMemory.GWModel P mk X U ζ c d) (hc : 0 < c) (hcd : c + d < 1)
    (hN0 : ∀ᵐ ω ∂P, 0 < mk.N (X [] ω)) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    variance (RstarNoMem mk X U ζ c d) P =
      d ^ 2 / (c + d) ^ 2 * variance (DirectedOpinion.NoMemory.Z X U ζ [] 0) P
        + rho2star P mk X * d ^ 2 / ((c + d) ^ 2 * ((c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X))
          * variance (DirectedOpinion.NoMemory.Z X U ζ [0] 0) P := by sorry

end DirectedOpinion.Memory
