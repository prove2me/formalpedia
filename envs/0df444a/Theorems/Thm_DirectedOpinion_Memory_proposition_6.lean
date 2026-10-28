-- Prove2me | Theorems.Thm_DirectedOpinion_Memory_proposition_6
-- name    : DirectedOpinion.Memory.proposition_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:59.392715+00:00
-- url     : https://prove2.me/theorems/9d56ed7a-8754-4e4b-a226-76a030b951fc
-- title:
--   Proposition 6 — on a Galton–Watson limit, Var(𝓜*) ≤ Var(𝓡*): memory does not increase the variance of the stationary opinion
-- statement:
--   Let the opinions live on a delayed marked Galton–Watson tree $\mathcal T(\mathcal X)$ with the Section 5.1 signals $\mathcal W_{\mathbf i}^{(k)}=d\mathcal Z_{\mathbf i}^{(k)}+\mathcal Q_{\mathbf i}\big(c-\sum_{j=1}^{\mathcal N_{\mathbf i}}\mathcal C_{(\mathbf i,j)}\big)$, with $c,d>0$ and $c+d<1$. Let $\mathcal M^*$ be the limiting root opinion of the general recursion
--   $$\mathcal M_{\mathbf i}^{(k+1)}=\sum_{j=1}^{\mathcal N_{\mathbf i}}\mathcal C_{(\mathbf i,j)}\mathcal M_{(\mathbf i,j)}^{(k)}+\mathcal W_{\mathbf i}^{(k)}+(1-c-d)\mathcal M_{\mathbf i}^{(k)},\qquad k\ge0,\tag{8}$$
--   and $\mathcal R^*$ the limiting root opinion of the no-memory recursion
--   $$\mathcal R_{\mathbf i}^{(k+1)}=\sum_{j=1}^{\mathcal N_{\mathbf i}}\frac{\mathcal C_{(\mathbf i,j)}}{c+d}\mathcal R_{(\mathbf i,j)}^{(k)}+\frac{\mathcal W_{\mathbf i}^{(k)}}{c+d},\qquad k\ge0.\tag{9}$$
--   If $P(\mathcal N_\varnothing>0)=P(\mathcal N_1>0)=1$, then
--   $$\mathrm{Var}(\mathcal M^*)\le\mathrm{Var}(\mathcal R^*).$$
--
--   Recursion (9) keeps the relative weights of the neighbours and of the media signal in (8) but removes the autoregressive term $(1-c-d)\mathcal M_{\mathbf i}^{(k)}$. The proposition says that this memory term can only make the stationary opinion less dispersed.
--
--   **Formalization Note.** The paper assumes "the assumptions of Theorem 2" with the Galton–Watson tree as the local limit. Those assumptions identify the tree's root opinion with the typical opinion of a large graph; the claim itself concerns only the limit tree. It is therefore stated on the tree under the Section 5 standing assumptions (independent marks, i.i.d. away from the root, signals of the Section 5.1 form), without the graph sequence: a generalization. "Limiting opinion" is the root series $\sum_{s\ge0}(\Delta^s\mathcal W^{(s)})(\varnothing)$ of the proof of Theorem 2 (p. 27): `Mstar` uses weights $\mathcal C$ and self-weight $1-c-d$; `RstarNoMem` uses weights $\mathcal C/(c+d)$, no self term, and signals $\mathcal W/(c+d)$. Both are bounded random variables, so both variances are genuine. The hypotheses $0<c$ and $c+d<1$ are the page's; $d>0$ is part of `GWModel`.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, pp. 17–18, Proposition 6

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting

namespace DirectedOpinion.Memory
open MeasureTheory ProbabilityTheory

/-- Proposition 6 (pp. 17–18): on a delayed marked Galton–Watson tree with the Section 5.1
signals, if c, d > 0, c + d < 1 and 𝓝_∅, 𝓝₁ > 0 a.s., then the root opinion 𝓜* of the
general recursion (8) has variance at most that of the root opinion 𝓡* of the no-memory
recursion (9). -/
theorem proposition_6 {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : DirectedOpinion.NoMemory.MarkFns M) (X : DirectedOpinion.NoMemory.Label → Ω → M)
    (U : DirectedOpinion.NoMemory.Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hGW : DirectedOpinion.NoMemory.GWModel P mk X U ζ c d) (hc : 0 < c) (hcd : c + d < 1)
    (hN0 : ∀ᵐ ω ∂P, 0 < mk.N (X [] ω)) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    variance (Mstar mk X U ζ c d) P ≤ variance (RstarNoMem mk X U ζ c d) P := by sorry

end DirectedOpinion.Memory
