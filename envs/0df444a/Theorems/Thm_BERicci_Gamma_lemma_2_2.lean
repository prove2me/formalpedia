-- Prove2me | Theorems.Thm_BERicci_Gamma_lemma_2_2
-- name    : BERicci.Gamma.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:24.415602+00:00
-- url     : https://prove2.me/theorems/d94955de-51a9-413f-b68e-521eb389ad64
-- title:
--   Lemma 2.2, p. 17 — four equivalent forms of a″ ≥ 2Ka′ + νg: distributional, weighted, integrated (2.27), Gronwall-type (2.28)
-- statement:
--   Let $t>0$, $K\in\mathbb R$, $\nu\ge0$, let $a\in C^1([0,t))$ with derivative $a'$, and let $g\in C^0([0,t))$. The following are equivalent:
--
--   1. $a''\ge 2Ka'+\nu g$ in $\mathscr D'(0,t)$, and pointwise in $[0,t)$ whenever $a\in C^2([0,t))$;
--   2. $\dfrac{d}{ds}\big(e^{-2Ks}a'(s)\big)\ge\nu e^{-2Ks}g(s)$ in $\mathscr D'(0,t)$;
--   3. for every $0\le s_1<s_2<t$ and every nonnegative $\zeta\in C^2([s_1,s_2])$,
--   $$\int_{s_1}^{s_2}a(\zeta''+2K\zeta')\,ds+[a'\zeta]_{s_1}^{s_2}-[a(\zeta'+2K\zeta)]_{s_1}^{s_2}\ge\nu\int_{s_1}^{s_2}g\zeta\,ds;\tag{2.27}$$
--   4. for every $0\le s_1<s_2<t$,
--   $$e^{-2K(s_2-s_1)}a'(s_2)\ge a'(s_1)+\nu\int_{s_1}^{s_2}e^{-2K(s-s_1)}g(s)\,ds.\tag{2.28}$$
--
--   This calculus lemma is applied with $a=\mathsf A_t[f;\varphi]$ and $g=4\mathsf A^\Delta_t[f;\varphi]$. It is how the weak Bakry–Émery inequality (2.33) is integrated into the pointwise estimates of Corollary 2.3.
--
--   **Formalization Note** The statement concerns real functions only and carries no Dirichlet-form hypothesis. A distributional inequality is tested against nonnegative smooth $\zeta$ with compact support in $(0,t)$ after integration by parts: (1) reads $\nu\int g\zeta\le\int a(\zeta''+2K\zeta')$, and (2) reads $\nu\int e^{-2Ks}g\zeta\le-\int e^{-2Ks}a'\zeta'$. The pointwise clause of (1) quantifies over a derivative $a''$ of $a'$ on $[0,t)$. Two hypotheses are added to the printed statement. In (3), $\zeta\ge0$ is required: the paper allows every $\zeta\in C^2$, for which (2.27) fails (replace $\zeta$ by $-\zeta$), and its proof only uses nonnegative $\zeta$. In (4), $s_2<t$ is required, since $a'$ is only defined on $[0,t)$.
-- source:
--   arXiv:1209.5786v4, Lemma 2.2, (2.27)–(2.28), p. 17

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Gamma_Calculus

namespace BERicci.Gamma

open MeasureTheory Topology
open scoped ENNReal

/-- Lemma 2.2, p. 17: for `a ∈ C¹([0,t))` with derivative `a'`, `g ∈ C⁰([0,t))`, `K ∈ ℝ` and `ν ≥ 0`,
the conditions (i)–(iv) are equivalent ((iii) for nonnegative test functions). -/
theorem lemma_2_2 (K ν t : ℝ) (ht : 0 < t) (hν : 0 ≤ ν)
    (a ap g : ℝ → ℝ) (ha : IsC1Ico t a ap) (hg : ContinuousOn g (Set.Ico 0 t)) :
    List.TFAE [L22Cond1 K ν t a ap g, L22Cond2 K ν t ap g, L22Cond3 K ν t a ap g,
      L22Cond4 K ν t ap g] := by sorry

end BERicci.Gamma
