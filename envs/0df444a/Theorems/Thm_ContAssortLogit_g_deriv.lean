-- Prove2me | Theorems.Thm_ContAssortLogit_g_deriv
-- name    : ContAssortLogit.g_deriv
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:35:05.054057+00:00
-- url     : https://prove2.me/theorems/ed1756f0-6c5e-4a7f-bdef-69f644aa1d89
-- title:
--   Proof of Lemma 4, p.37 — $g'(y)=(g(y)-w(y))\,\xi(y)$ on $(0,1)$
-- statement:
--   Let $w$ be a revenue function and $v\in\mathcal V(\underline v,\overline v,D)$. Let $g(y)=r([y,1],v)$ and $\xi(y)=v(y)/(1+\int_y^1 v(x)\,dx)$. Then for every $y\in(0,1)$, $g$ is differentiable at $y$ and
--   $$g'(y)=\frac{d}{dy}\,\frac{\int_y^1 v(x)w(x)\,dx}{1+\int_y^1 v(x)\,dx}=\big(r([y,1],v)-w(y)\big)\cdot\frac{v(y)}{1+\int_y^1 v(x)\,dx}=\big(g(y)-w(y)\big)\cdot\xi(y).$$
--
--   This identifies the optimal threshold as a solution of $g(y)=w(y)$ and is the starting point of the curvature bound (27).
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: the $g'$ display, with $\xi$ defined for $y\in[0,1]$ → the identity $g'(y)=(g(y)-w(y))\xi(y)$ at every $y\in(0,1)$; reason: at $y=0$ it can fail: $v=1$ on $(0,1]$, $v(0)=2$, $w(x)=x$ lies in $\mathcal V(1/2,3,0)$, the right derivative of $g$ at $0$ is $(g(0)-w(0))/2$ but the formula gives $(g(0)-w(0))\cdot 2/2$, and $g(0)=1/4\ne0=w(0)$; the paper uses the display on $(0,1)$ in (27)
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, proof of Lemma 4, p.37, display "g′(y) = …"

import Mathlib
import Definitions.Def_ContAssortLogit_Model
open MeasureTheory Set

namespace ContAssortLogit

/-- **The derivative of `g`** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, proof of Lemma 4,
p.37): `g′(y) = (r([y, 1], v) − w(y)) · v(y) / (1 + ∫_y^1 v(x) dx) = (g(y) − w(y)) · ξ(y)`, for
`y ∈ (0, 1)`, where `g(y) = r([y, 1], v)` and `ξ(y) = v(y) / (1 + ∫_y^1 v(x) dx)`.

**Formalization Note.** Stated at interior points `y ∈ (0, 1)`, where `v` is differentiable and
hence continuous; at `y = 0` the identity can fail because `v(0)` is unconstrained by continuity. -/
theorem g_deriv (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) :
    ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (gfun w v) ((gfun w v y - w y) * xi v y) y := by sorry

end ContAssortLogit
