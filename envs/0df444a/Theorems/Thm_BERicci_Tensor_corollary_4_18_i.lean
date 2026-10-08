-- Prove2me | Theorems.Thm_BERicci_Tensor_corollary_4_18_i
-- name    : BERicci.Tensor.corollary_4_18_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:50.231665+00:00
-- url     : https://prove2.me/theorems/dc70331a-0353-40d7-bdb9-d749f0f93d2a
-- title:
--   Corollary 4.18 (i), p. 58 — a length space with quadratic Cheeger energy and the gradient bound (4.30) is RCD(K,∞)
-- statement:
--   Let $(X,\mathsf d,\mathfrak m)$ be a complete separable metric space with a Borel measure $\mathfrak m$ satisfying (MD+exp): $\operatorname{supp}\mathfrak m=X$, $\mathfrak m(B_r(x))<\infty$ for all $x\in X$, $r>0$, and $\mathfrak m(B_r(x_0))\le Me^{cr^2}$ for some $x_0\in X$, $M>0$, $c\ge0$ and all $r\ge0$. Assume (QCh): the Cheeger energy $\mathsf{Ch}$ is quadratic, i.e. $\mathcal E=2\mathsf{Ch}$ is a strongly local Dirichlet form, every $f\in D(\mathsf{Ch})$ has a Carré du champ $\Gamma(f)$, and $|Df|_w^2=\Gamma(f)$. Let $(\mathsf P_t)_{t\ge0}$ be the heat flow of $\mathcal E$ and $K\in\mathbb R$.
--
--   If $(X,\mathsf d)$ is a length space and, for every $f\in D(\mathsf{Ch})$ with $|Df|_w\le1$ and every $t>0$,
--   $$\mathsf P_tf\in\mathrm{Lip}_b(X),\qquad |D\mathsf P_tf|^2\le e^{-2Kt}\,\mathsf P_t\big(|Df|_w^2\big)\quad\mathfrak m\text{-a.e. in }X,\tag{4.30}$$
--   then $(X,\mathsf d,\mathfrak m)$ is an $\mathrm{RCD}(K,\infty)$ space.
--
--   This is the characterization of $\mathrm{RCD}(K,\infty)$ through the pointwise gradient bound that the proof of Theorem 5.1 uses: it reduces the stability of $\mathrm{RCD}(K,\infty)$ under products to the stability of the length property and of (4.30).
--
--   **Formalization Note** The minimal weak gradient is written through (QCh) as $|Df|_w^2=\Gamma(f)$, the Carré du champ density of $\mathcal E=2\mathsf{Ch}$; the identity itself is part of (QCh) and is not restated. "$\mathsf P_tf\in\mathrm{Lip}_b(X)$" is the existence of a bounded Lipschitz $u$ with $u=\mathsf P_tf$ $\mathfrak m$-a.e., and $|D\mathsf P_tf|$ is the slope of $u$ (unique since $\operatorname{supp}\mathfrak m=X$). Only the "if" direction of (i) is stated; the "only if" and parts (ii), (iii) are not posed.
-- source:
--   arXiv:1209.5786v4, Corollary 4.18 (i), (4.30), p. 58; (QCh), p. 26; (MD), (MD.exp), p. 21

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Tensor_Product
open MeasureTheory Filter Topology
open scoped ENNReal

namespace BERicci.Tensor

/-- **Corollary 4.18 (i)**, p. 58, the "if" direction. A metric measure space `(X, d, m)` with
`(MD+exp)` (complete separable binders, `supp m = X`, (MD.b), (MD.exp)) whose Cheeger energy is
quadratic, (QCh): `E = 2 Ch` is a strongly local Dirichlet form admitting a Carré du champ on its
whole BERicci.Gamma.domain, with `|Df|_w² = Γ(f)`. If `(X, d)` is a length space and the heat flow `P` of
`E = 2 Ch` satisfies (4.30) — for every `f ∈ D(Ch)` with `|Df|_w ≤ 1` and every `t > 0`,
`P_t f ∈ Lip_b(X)` and `|D P_t f|² ≤ e^{−2Kt} P_t(|Df|_w²)` m-a.e. — then `(X, d, m)` is an
`RCD(K, ∞)` space. `|Df|_w²` is written as the Carré du champ density `Γ(f)` of `E = 2 Ch`, as
(QCh) allows; `|D P_t f|` is the BERicci.Gamma.slope of the bounded Lipschitz representative of `P_t f`. -/
theorem corollary_4_18_i
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (hfull : m.IsOpenPosMeasure) (hb : BERicci.Gamma.MDb m) (hexp : BERicci.Gamma.MDexp m)
    (hQCh : BERicci.Gamma.IsDirichletForm m (fun f => 2 * BERicci.Gamma.cheeger m f))
    (hQChloc : BERicci.Gamma.IsStronglyLocal m (fun f => 2 * BERicci.Gamma.cheeger m f))
    (hQChG : ∀ f : X → ℝ, BERicci.Gamma.cheeger m f < ⊤ → ∃ g : X → ℝ,
      BERicci.Gamma.IsCarreDuChamp m (fun f => 2 * BERicci.Gamma.cheeger m f) f g)
    (P : ℝ → (X → ℝ) → X → ℝ) (hP : BERicci.Gamma.IsHeatSemigroup m (fun f => 2 * BERicci.Gamma.cheeger m f) P)
    (K : ℝ) (hlen : BERicci.Gamma.IsLengthSpace X)
    (h430 : ∀ f g : X → ℝ, BERicci.Gamma.IsCarreDuChamp m (fun f => 2 * BERicci.Gamma.cheeger m f) f g → g ≤ᵐ[m] 1 →
      ∀ t : ℝ, 0 < t → ∃ u : X → ℝ, BERicci.Gamma.IsLipB u ∧ u =ᵐ[m] P t f ∧
        ∀ᵐ x ∂m, BERicci.Gamma.slope u x ^ 2 ≤ ENNReal.ofReal (Real.exp (-2 * K * t) * P t g x)) :
    BERicci.Gamma.IsRCDInfty m K := by sorry

end BERicci.Tensor
