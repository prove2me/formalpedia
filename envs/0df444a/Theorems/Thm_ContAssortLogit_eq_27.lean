-- Prove2me | Theorems.Thm_ContAssortLogit_eq_27
-- name    : ContAssortLogit.eq_27
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:35:28.417676+00:00
-- url     : https://prove2.me/theorems/fe7d4768-76d8-4fcb-ab87-7428a96c4ebf
-- title:
--   (27), p.37 — $\sup_{y\in(0,1)}\{-g''(y)\}\le C_0$
-- statement:
--   Let $w$ be a revenue function, $v\in\mathcal V(\underline v,\overline v,D)$, and let $M_w$ be an upper bound of $w'$ on $[0,1]$. Then for every $y\in(0,1)$ the second derivative $g''(y)$ exists and
--   $$-g''(y)\le C_0:=D+2\overline v^{\,2}+M_w\,\overline v.$$
--   With $M_w=\sup_{[0,1]}w'$ and $D=\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|$ this is the paper's constant $C_0=\sup_{y\in(0,1),v\in\mathcal V}\{|v'(y)|+2\overline v^2\}+\sup_{y\in[0,1]}w'(y)\,\overline v$ (p.38), so
--   $$\sup_{y\in(0,1)}\{-g''(y)\}\le C_0.\tag{27}$$
--
--   The constant does not depend on $v\in\mathcal V$; this uniformity is what makes the regret bound of Theorem 1 worst-case.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - encoding: $\sup_{y\in(0,1)}\{-g''(y)\}\le C_0$ with $C_0=\sup_{y\in(0,1),v\in\mathcal V}\{|v'(y)|+2\overline v^2\}+\sup_{y\in[0,1]}w'(y)\overline v$ → for every $y\in(0,1)$, $g''(y)$ exists and $-g''(y)\le D+2\overline v^2+M_w\overline v$ for every upper bound $M_w$ of $w'$ on $[0,1]$; reason: the supremum of $|v'|$ over $(0,1)\times\mathcal V(\underline v,\overline v,D)$ is $D$, and a bound for every upper bound $M_w$ is the bound for $M_w=\sup w'$; existence of $g''$ is presupposed by the display
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, proof of Lemma 4, (27), p.37, and the definition of C₀, p.38

import Mathlib
import Definitions.Def_ContAssortLogit_Model
open MeasureTheory Set

namespace ContAssortLogit

/-- **Inequality (27)** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, proof of Lemma 4,
pp.37–38): `sup_{y ∈ (0,1)} {−g″(y)} ≤ C₀`, with the constant of p.38
`C₀ = sup_{y ∈ (0,1), v ∈ 𝒱} {|v′(y)| + 2v̄²} + sup_{y ∈ [0,1]} w′(y) v̄`.

In Lean: for every `y ∈ (0, 1)` the second derivative `g″(y)` exists (as the derivative of `g′` at
`y`) and `−g″(y) ≤ D + 2v̄² + M_w v̄`, for every upper bound `M_w` of `w′` on `[0, 1]`.

**Formalization Note.** The supremum of `|v′|` over `(0,1) × 𝒱(v̲, v̄, D)` is `D` (small
oscillations of slope up to `D` stay inside `[v̲, v̄]`), and stating the bound for every upper
bound `M_w` of `w′` is equivalent to stating it with `M_w = sup_{[0,1]} w′`. -/
theorem eq_27 (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) (Mw : ℝ)
    (hMw : ∀ x ∈ Icc (0 : ℝ) 1, derivWithin w (Icc 0 1) x ≤ Mw) :
    ∀ y ∈ Ioo (0 : ℝ) 1, ∃ g2 : ℝ, HasDerivAt (deriv (gfun w v)) g2 y ∧
      -g2 ≤ D + 2 * vhi ^ 2 + Mw * vhi := by sorry

end ContAssortLogit
