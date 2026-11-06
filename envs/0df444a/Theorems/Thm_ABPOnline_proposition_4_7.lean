-- Prove2me | Theorems.Thm_ABPOnline_proposition_4_7
-- name    : ABPOnline.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:52.854191+00:00
-- url     : https://prove2.me/theorems/3799dc91-d0e8-4880-9f8e-33120516de5a
-- title:
--   Proposition 4.7 — Algorithm 1 succeeds at level $r$ under the strict inequalities (25)
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$. Fix a constraint density $\alpha>0$ and an even integer $p>4$. Let $a>r$ and $c_F>0$, let $(h_0,s_p,v)$ be a final-block triple with the property of Lemma 4.5 for $(p,c_F)$, let $T=1-h$ be rational with $0<h<h_0$, and let $\beta$ be a bounded simple predictable control on $[0,T]$ of the form in Definition 4.2 with
--   $$
--   \|\beta\|_{\infty,2}<c_\alpha,\qquad \frac1h\|(a-Y^\beta_T)_+\|_{L^p}+c_F<c_\alpha,\qquad s_p(h,c_F)<a-r .
--   $$
--   Then Algorithm 1, with first-stage control $\beta$, target $a$ and final-block feedback $v$, satisfies
--   $$
--   \mathbb P\Big(\min_{i\le M}X_{N,i}\ge r\Big)\longrightarrow1
--   $$
--   for every integer sequence $M_N$ with $M_N/N\to\alpha$.
--
--   Its hypotheses are exactly the inequalities that Proposition 4.8 arranges from the Brownian control problem.
--
--   Differences from the source:
--   - generalization: Algorithm 1 with the feedback v_N, h₀(p, c_F) and s_p of Lemma 4.5 → any triple (h₀, s_p, v) with IsFinalBlockFeedback p c_F h₀ s_p v; reason: the paper's triple has this property by Lemma 4.5, so the statement specializes to the source
--   - reading: T = 1 − h → T rational with (T : ℝ) = 1 − h; reason: Algorithm 1 takes a rational T, and Definition 4.2 (s_L = T) forces it
--   - encoding: (1/h)‖(a − Y^β_T)₊‖_{L^p} + c_F < c_α → eLpNorm((a − Y^β_T)₊, p) < ENNReal.ofReal(h(c_α − c_F)); reason: equivalent for h > 0, with no junk value of an infinite norm
--   - encoding: ‖β‖_{∞,2} and Y^β_T for a Brownian motion → computed on the given standard Brownian motion B on [0, 1]; reason: these quantities depend only on the law of B
--   - encoding: M/N → α (every integer sequence M_N) → ∀ Mseq : ℕ → ℕ with (Mseq N : ℝ)/N → α; reason: the same; (Mseq N)/N is 0 at N = 0, which does not affect the limit
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Proposition 4.7, (25)–(26), p.15 (PDF p.16)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_IsOnlineAlg
import Definitions.Def_ABPOnline_Estar
import Definitions.Def_ABPOnline_IsFinalBlockFeedback
import Definitions.Def_ABPOnline_alg1

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ABPOnline

/-- **Proposition 4.7** (arXiv:2609.02124, printed p.15, PDF p.16). Fix a constraint density
`α > 0` and an even integer `p > 4`. Let `a > r` and `c_F > 0`, let `T = 1 − h` with
`0 < h < h₀(p, c_F)`, and let `β` be a bounded simple predictable control on `[0,T]` of the form in
Definition 4.2 with (25): `‖β‖_{∞,2} < c_α`, `(1/h)‖(a − Y^β_T)₊‖_{L^p} + c_F < c_α`,
`s_p(h, c_F) < a − r`. Then Algorithm 1, with first-stage control `β`, target `a`, and final-block
budget `c_F`, satisfies `P(min_{i≤M} X_{N,i} ≥ r) → 1` (26) whenever `M/N → α`.

**Formalization Note** `(h₀, s_p, v)` is any triple with the property of Lemma 4.5 for `(p, c_F)`
(`IsFinalBlockFeedback`); Algorithm 1 uses the feedback `v`. The paper's `h₀`, `s_p`, `v_N` are one
such triple. `T` is rational, as Algorithm 1 requires. The quantities in (25) are computed on a
standard Brownian motion `B`; the second inequality is written
`‖(a − Y^β_T)₊‖_{L^p} < h(c_α − c_F)`. "Whenever `M/N → α`" is every integer sequence `M_N` with
`M_N/N → α`. -/
theorem proposition_4_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianOn1 B P) (α : ℝ) (hα : 0 < α) (p : ℕ) (hp : Even p)
    (hp4 : 4 < p) (a r cF : ℝ) (har : r < a) (hcF : 0 < cF) (h₀ : ℝ) (sp : ℝ → ℝ)
    (v : ℕ → ℕ → ℝ → ℝ → ℝ) (hv : IsFinalBlockFeedback p cF h₀ sp v) (h : ℝ) (hh : 0 < h)
    (hh₀ : h < h₀) (T : ℚ) (hT : (T : ℝ) = 1 - h) (β : SimpleCtrl) (hβ : β.IsValidOn T)
    (h25a : ctrlNormOn P T (β.proc B) < ENNReal.ofReal (cAlpha α))
    (h25b : eLpNorm (fun ω => max (a - ctrlTerminal B (β.proc B) T ω) 0) p P <
      ENNReal.ofReal (h * (cAlpha α - cF)))
    (h25c : sp h < a - r) :
    ∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
      Tendsto (fun N : ℕ => gaussMat (Mseq N) N (successSet (alg1 T a β v (Mseq N) N) r))
        atTop (𝓝 1) := by sorry

end ABPOnline
