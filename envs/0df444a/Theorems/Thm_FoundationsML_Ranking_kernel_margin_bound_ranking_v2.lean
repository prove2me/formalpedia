-- Prove2me | Theorems.Thm_FoundationsML_Ranking_kernel_margin_bound_ranking_v2
-- name    : FoundationsML.Ranking.kernel_margin_bound_ranking_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:41.753965+00:00
-- url     : https://prove2.me/theorems/81497bf2-12ff-4e4e-8086-d8ed9b145949
-- title:
--   Corollary 10.2 — margin bound for ranking with kernel-based hypotheses (corrected: $K(x,x)\le r^2$; $m\ge1$)
-- statement:
--   **Statement (Corollary 10.2, p. 243, PDF p. 260; corrected transcription).** Let $K:X\times X\to\mathbb R$ be a PDS kernel with feature map $\Phi$ and $K(x,x)\le r^2$ for all $x\in X$, and let $H=\{x\mapsto w\cdot\Phi(x):\|w\|_H\le\Lambda\}$; $f$ is a $\{-1,+1\}$-valued (measurable) preference function. Fix $\rho>0$. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over a sample of size $m\ge1$, for all $h\in H$:
--   $$R(h) \le \hat R_{S,\rho}(h) + 4\sqrt{\frac{r^2\Lambda^2/\rho^2}{m}} + \sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   **Formalization Note.** The retired version allowed $m=0$ (every sample-dependent term is Lean's $x/0=0$) and transcribed the printed hypothesis "$r=\sup_x K(x,x)$" literally as $K(x,x)\le r$. The printed corollary is a misprint: it is Theorem 10.1 combined with Theorem 6.12, whose bound $\hat R_S(H)\le\sqrt{r^2\Lambda^2/m}$ requires $K(x,x)\le r^2$ (exactly as Corollary 9.4 and Theorem 6.12 state it), and with $K(x,x)\le r$ the printed bound is false for $r<1$: with an orthogonal feature map $\Phi(x_i)=\sqrt r\,e_i$ on many points, pairs drawn uniformly with $f\equiv+1$, every $h$ has $R(h)\ge\tfrac12$ while a $w$ of norm $\Lambda$ fitting the sampled pairs has $\hat R_{S,\rho}(h_w)=0$ for $\rho=\sqrt{2r}\Lambda/\sqrt m$, and then $4\sqrt{r^2\Lambda^2/\rho^2/m}=2\sqrt{2r}<\tfrac12$. The hypothesis is therefore $K(x,x)\le r^2$, $r\ge0$. Also: $m\ge1$, $\delta\in(0,1)$ (standing conventions), and the book's standing measurability (footnote 2, p. 10) of $f$ and of the hypotheses $x\mapsto\langle w,\Phi(x)\rangle$ is explicit.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 243, Corollary 10.2 (PDF p. 260) — corrected transcription: the kernel bound is K(x,x) ≤ r² (as in Theorem 6.12 and Corollary 9.4), not K(x,x) ≤ r

import Mathlib
import Definitions.Def_FoundationsML_Ranking_GeneralizationError
import Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Ranking_IsPDS
import Definitions.Def_FoundationsML_Ranking_LinearKernelHypothesisClass

open MeasureTheory

namespace FoundationsML.Ranking

/-- Corollary 10.2 (Margin bound for ranking with kernel-based hypotheses; Mohri, Rostamizadeh
& Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 243, PDF p. 260),
corrected transcription. Let `K` be a PDS kernel with feature map `Φ` and `K(x,x) ≤ r²` for
all `x`, and `H = {x ↦ w·Φ(x) : ‖w‖_H ≤ Λ}`; `f` is a `{−1,+1}`-valued preference function.
Fix `ρ > 0`. Then, for any `δ > 0`, with probability at least `1 − δ` over a sample of size
`m ≥ 1`, for all `h ∈ H`:
`R(h) ≤ R̂_{S,ρ}(h) + 4·sqrt(r²Λ²/ρ²/m) + sqrt(log(1/δ)/(2m))`.

**Formalization Note.** Replaces `kernel_margin_bound_ranking`, which allowed `m = 0` (every
sample-dependent term is then Lean's `x / 0 = 0`) and transcribed the printed hypothesis
`r = sup_x K(x,x)` literally as `K(x,x) ≤ r`. The printed corollary is a misprint: it is
Theorem 10.1 combined with Theorem 6.12, whose bound `sqrt(r²Λ²/m)` requires `K(x,x) ≤ r²`
(as in Corollary 9.4 and Theorem 6.12), and with `K(x,x) ≤ r` the stated bound is false for
`r < 1` (an orthogonal feature map with `K(x,x) = r` small and many points gives
`R(h) ≥ 1/2`, `R̂_{S,ρ}(h) = 0` and `4 sqrt(r²Λ²/ρ²/m) → 0`). The hypothesis is therefore
`K(x,x) ≤ r²`, `r ≥ 0`. Also: `m ≥ 1`, `δ ∈ (0,1)` (standing conventions), and the book's
standing measurability (footnote 2, p. 10) of `f` and of the hypotheses `x ↦ ⟪w, Φ(x)⟫` is
explicit. -/
theorem kernel_margin_bound_ranking_v2
    {X Hb : Type*} [MeasurableSpace X] (D : Measure (X × X)) [IsProbabilityMeasure D]
    [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (K : X → X → ℝ) (Φ : X → Hb) (hK : IsPDS K)
    (hΦ : ∀ x y, K x y = (inner (𝕜 := ℝ) (Φ x) (Φ y) : ℝ))
    (hΦmeas : ∀ w : Hb, Measurable (fun x => (inner (𝕜 := ℝ) w (Φ x) : ℝ)))
    (r : ℝ) (hr : 0 ≤ r) (hrK : ∀ x, K x x ≤ r ^ 2)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (f : X × X → ℝ) (hf : ∀ p, f p = 1 ∨ f p = -1) (hf_meas : Measurable f)
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ LinearKernelHypothesisClass Φ Λ,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            4 * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Ranking
