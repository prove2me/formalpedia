-- Prove2me | Theorems.Thm_DistTransform_Distortion_chambers_quantile
-- name    : DistTransform.Distortion.chambers_quantile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:23.610751+00:00
-- url     : https://prove2.me/theorems/40501f4d-113b-4422-938e-b666056fac20
-- title:
--   Proof of Theorem 1, p. 7 — Chambers (2009), Thm 1: a monotone, shape-covariant functional on M∞ is a left or right quantile at a fixed level
-- statement:
--   Let $q$ be a real-valued functional on $\mathcal M_\infty$, the distributions on $\mathbb R$ with bounded support. Suppose
--
--   1. $q(F)\le q(G)$ whenever $F,G\in\mathcal M_\infty$ and $F\preceq_{\mathrm{st}}G$, and
--   2. $q\big(T^{[\varphi]}(F)\big)=\varphi(q(F))$ for every $F\in\mathcal M_\infty$ and every strictly increasing continuous $\varphi$ with $\varphi(\mathbb R)=\mathbb R$.
--
--   Then there is a level $\alpha\in[0,1]$, not depending on $F$, such that either
--   $$
--   \alpha>0\ \text{ and }\ q(F)=F^{-1}(\alpha)\ \text{ for all }F\in\mathcal M_\infty,
--   $$
--   or
--   $$
--   \alpha<1\ \text{ and }\ q(F)=F^{-1}_+(\alpha)\ \text{ for all }F\in\mathcal M_\infty.
--   $$
--
--   This is Theorem 1 of Chambers (2009), *An axiomatization of quantiles on the domain of distribution functions*, Mathematical Finance 19(2), together with its footnote, in the form in which Liu, Schied and Wang invoke it for $q=q_p^T$ in the proof of their Theorem 1. It is the step that turns the abstract properties of $T$ into a quantile representation.
--
--   **Formalization Note** The paper cites this result and does not prove it. It is stated on $\mathcal M_\infty$ and for real-valued functionals because that is how the proof applies it. The side conditions $\alpha>0$ for the left quantile and $\alpha<1$ for the right quantile are the paper's "if $h(p)=1$, $p\in E$; if $h(p)=0$, $p\notin E$": the left quantile at level $0$ and the right quantile at level $1$ are infinite.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), p. 7, the application of Theorem 1 of Chambers (2009) before Eq. (2)

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace DistTransform.Distortion

/-- Proof of Theorem 1, p. 7, Theorem 1 of Chambers (2009) as invoked before eq. (2): a
real-valued functional on `M∞` that is monotone in `⩽st` and satisfies
`q(T^[φ](F)) = φ(q(F))` for every shape transform `φ` is a left or a right quantile at a level
`α ∈ [0, 1]` that does not depend on `F` (left quantile only for `α > 0`, right quantile only
for `α < 1`). -/
theorem chambers_quantile (q : ProbabilityMeasure ℝ → ℝ)
    (hq_mono : ∀ F ∈ Minf, ∀ G ∈ Minf, StLE F G → q F ≤ q G)
    (hq_shape : ∀ φ : ℝ ≃o ℝ, ∀ F ∈ Minf, q (shape φ F) = φ (q F)) :
    ∃ α ∈ Set.Icc (0 : ℝ) 1,
      (0 < α ∧ ∀ F ∈ Minf, q F = leftQuantile F α) ∨
        (α < 1 ∧ ∀ F ∈ Minf, q F = rightQuantile F α) := by sorry

end DistTransform.Distortion
