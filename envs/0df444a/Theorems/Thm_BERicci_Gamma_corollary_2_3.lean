-- Prove2me | Theorems.Thm_BERicci_Gamma_corollary_2_3
-- name    : BERicci.Gamma.corollary_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:32.718991+00:00
-- url     : https://prove2.me/theorems/3b2bbd06-c392-4a01-84cf-5d0adfd76ad2
-- title:
--   Corollary 2.3, pp. 18–19 — (i) pointwise Γ₂, (ii) along the flow, (iii) weak BE (2.33), (iv) (2.34), (v) local Poincaré, (vi) gradient bound (2.35) are equivalent, and imply 𝔾 = 𝕍
-- statement:
--   Let $\mathcal E$ be a strongly local symmetric Dirichlet form on $L^2(X,m)$ with heat flow $(\mathsf P_t)_{t\ge0}$ and generator $\Delta_{\mathcal E}$, as in (2.1), and let $K\in\mathbb R$ and $\nu\ge0$. The following conditions are equivalent:
--
--   1. **(i)** For every $(f,\varphi)\in D(\Gamma_2)$ with $\varphi\ge0$,
--   $$\Gamma_2[f;\varphi]\ge K\,\Gamma[f;\varphi]+\nu\int_X(\Delta_{\mathcal E}f)^2\varphi\,dm.$$
--   2. **(ii)** For every $f\in L^2(X,m)$ and every nonnegative $\varphi\in D(\Delta_{\mathcal E})\cap L^\infty(X,m)$ with $\Delta_{\mathcal E}\varphi\in L^\infty(X,m)$,
--   $$\mathsf C_t[f;\varphi](s)\ge K\,\mathsf B_t[f;\varphi](s)+2\nu\,\mathsf A^\Delta_t[f;\varphi](s)\qquad\text{for every }0\le s<t.\tag{2.32}$$
--   3. **(iii)** For every $f\in L^2(X,m)$, every nonnegative $\varphi\in L^2\cap L^\infty(X,m)$ and $t>0$,
--   $$\frac{\partial^2}{\partial s^2}\mathsf A_t[f;\varphi](s)\ge 2K\frac{\partial}{\partial s}\mathsf A_t[f;\varphi](s)+4\nu\,\mathsf A^\Delta_t[f;\varphi](s)\quad\text{in }\mathscr D'(0,t).\tag{2.33}$$
--   4. **(iv)** For every $f\in L^2(X,m)$ and $t>0$, $\mathsf P_tf\in\mathbb G$ and, $m$-a.e. in $X$,
--   $$I_{2K}(t)\,\Gamma(\mathsf P_tf)+2\nu I_{2K,2}(t)(\Delta_{\mathcal E}\mathsf P_tf)^2\le\tfrac12\mathsf P_t(f^2)-\tfrac12(\mathsf P_tf)^2.\tag{2.34}$$
--   5. **(v)** $\mathbb G=\mathbb V$ and, for every $f\in\mathbb V$ and $t>0$, $m$-a.e. in $X$,
--   $$\tfrac12\mathsf P_t(f^2)-\tfrac12(\mathsf P_tf)^2+2\nu I_{-2K,2}(t)(\Delta_{\mathcal E}\mathsf P_tf)^2\le I_{-2K}(t)\,\mathsf P_t\Gamma(f).$$
--   6. **(vi)** $\mathbb G$ is dense in $L^2(X,m)$ and, for every $f\in\mathbb G$ and $t>0$, $\mathsf P_tf\in\mathbb G$ and, $m$-a.e. in $X$,
--   $$\Gamma(\mathsf P_tf)+2\nu I_{-2K}(t)(\Delta_{\mathcal E}\mathsf P_tf)^2\le e^{-2Kt}\,\mathsf P_t\Gamma(f).\tag{2.35}$$
--
--   If one of them holds, then $\mathbb G=\mathbb V$, i.e. $\mathcal E$ admits a carré du champ on its whole domain.
--
--   Here $\mathsf A_t$, $\mathsf A^\Delta_t$, $\mathsf B_t$, $\mathsf C_t$ are the functions (2.23)–(2.24) along the heat flow, $I_K$, $I_{K,2}$ are (2.29), and $\mathsf P_t$ acts on $f^2$ and $\Gamma(f)$ through its extension to $L^1$. Condition (iii) is the one used to define $BE(K,N)$ with $N=1/\nu$ (Definition 2.4). The equivalence of the weak forms (iii)–(vi) with the pointwise $\Gamma_2$-inequality (i) is what allows the paper to work with $BE(K,N)$ under minimal regularity.
--
--   **Formalization Note** Condition (v) is stated with the coefficient $I_{-2K}(t)$ on $\mathsf P_t\Gamma(f)$; the paper prints $I_{-2K,2}(t)$. As printed, that coefficient is $\sim t^2/2$ while the left side is of order $t\,\Gamma(f)$ as $t\downarrow0$, so printed (v) fails for small $t$ for the heat flow on $\mathbb R$ (take $f(x)=x$ locally: $t\le t^2/2$), which satisfies (iii) with $K=\nu=0$. The paper proves (iii) ⇒ (v) "by (2.31)", which with $\mathsf a=\mathsf A_t[f;\varphi]$, $\tau\uparrow t$ gives exactly $I_{-2K}(t)$ (the classical local Poincaré inequality). (v) is stated for $t>0$; at $t=0$ both sides vanish. The other hypotheses and conventions are as follows.
--   - The standing hypotheses (2.1) are the binders `hE`, `hloc` and `hP` ($\mathsf P$ is pinned by `IsHeatSemigroup`), and `hP1` pins the $L^1$ extension.
--   - (iii) is `BE m E P K ν` of the Setting, whose extra conjunct $\nu\ge0$ is a hypothesis here.
--   - In (i) and (ii), $\Gamma$ and $\Gamma_2$ are the predicates `IsGammaVal`/`IsGamma2Val`, and the inequality is required wherever they are defined. The paper's $\Gamma$ is only defined on $\mathbb V\times\mathbb V\times\mathbb V_\infty$, so $\Gamma[f;\Delta_{\mathcal E}\varphi]$ is undefined when $\Delta_{\mathcal E}\varphi\notin\mathbb V$.
--   - $\Gamma(\cdot)$ and $\Delta_{\mathcal E}$ are a.e.-unique witnesses.
--   - $\mathbb G=\mathbb V$ is `carreDomain m E = domain E`.
-- source:
--   arXiv:1209.5786v4, Corollary 2.3 (i)–(vi) and the final sentence, (2.32)–(2.35), pp. 18–19

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Gamma_Calculus

namespace BERicci.Gamma

open MeasureTheory Topology
open scoped ENNReal

/-- Corollary 2.3, pp. 18–19: conditions (i)–(vi) are equivalent, and each of them implies `𝔾 = 𝕍`.
(iii) is `BE m E P K ν` (Definition 2.4 through (2.33)); (v) is `BECond5`, with the printed coefficient
`I_{−2K,2}(t)` of `P_t Γ(f)` corrected to `I_{−2K}(t)`. -/
theorem corollary_2_3
    {X : Type*} [MeasurableSpace X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞)
    (hE : IsDirichletForm m E) (hloc : IsStronglyLocal m E)
    (P P1 : ℝ → (X → ℝ) → X → ℝ)
    (hP : IsHeatSemigroup m E P) (hP1 : IsL1Extension m P P1)
    (K ν : ℝ) (hν : 0 ≤ ν) :
    List.TFAE [BECond1 m E K ν, BECond2 m E P K ν, BE m E P K ν,
        BECond4 m E P P1 K ν, BECond5 m E P P1 K ν, BECond6 m E P P1 K ν] ∧
      (BE m E P K ν → carreDomain m E = domain E) := by sorry

end BERicci.Gamma
