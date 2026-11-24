-- Prove2me | Theorems.Thm_CustomHedge_Exist_Supplement_theorem_2
-- name    : CustomHedge.Exist.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:38:50.043837+00:00
-- url     : https://prove2.me/theorems/049e9f4f-3d60-432e-8be1-ef863b7a8f62
-- title:
--   Theorem 2, p. 12 (corrected: second term of (9)) — under a joint density, the optimal claims are payoff functions and H*₀ solves the Fredholm equation (8)
-- statement:
--   Let $X,Y,I$ be $\mathbb R^N$-valued random variables on $(\Omega,\mathcal F,\mathbb P)$ that admit a joint density $f_{XYI}$ under $\mathbb P$, with marginals $f_{XY},f_{XI},f_X,f_I$, and let $f^{\mathbb Q}_X,f^{\mathbb Q}_I$ be densities of the laws of $X$ and $I$ under the risk-neutral probability $\mathbb Q$. Assume the standing assumptions of the market (position $\pi(X,Y)\in L^2$, pricing kernel $d\mathbb Q/d\mathbb P\in L^2$ positive with mean one, $\varrho\ge0$, $a>0$) and that the maximal correlation satisfies $r_{XI}<1$.
--
--   Let $(H^*,G^*)$ be an optimal combined claim pair of problem (4), and $H^*_0=H^*-\mathbb E[H^*]$, $G^*_0=G^*-\mathbb E[G^*]$ its value-centered claims. Then there are Borel payoff functions $H^*_0(x)\in L^2_X$ and $G^*_0(i)\in L^2_I$ with $H^*_0=H^*_0(X)$ and $G^*_0=G^*_0(I)$ a.s., such that
--   $$H^*=H^*_0(X)-c^*_H,\qquad G^*=G^*_0(I)-c^*_G,\qquad c^*_H=\mathbb E_{\mathbb Q}[H^*_0(X)],\quad c^*_G=\mathbb E_{\mathbb Q}[G^*_0(I)],$$
--   and $H^*_0$ solves the Fredholm equation of the second kind
--   $$H^*_0(x)=\Pi^X_0(x)+\int_{\mathbb R^N}k(x,\xi)\,H^*_0(\xi)\,d\xi\qquad\text{for } \mathbb P_X\text{-a.e. } x,\qquad(8)$$
--   with kernel $k(x,\xi)=\int\frac{f_{XI}(x,i)}{f_X(x)f_I(i)}f_{XI}(\xi,i)\,di$ and term
--   $$\Pi^X_0(x)=-\int\pi(x,y)\frac{f_{XY}(x,y)}{f_X(x)}dy+\int_{\mathbb R^{3N}}\pi(\xi,y)\frac{f_{XYI}(\xi,y,i)f_{XI}(x,i)}{f_X(x)f_I(i)}d\xi\,dy\,di-\frac{\varrho}{a}\Big(\frac{f^{\mathbb Q}_X(x)}{f_X(x)}-\int f^{\mathbb Q}_I(i)\frac{f_{XI}(x,i)}{f_X(x)f_I(i)}di\Big).$$
--
--   The theorem turns the abstract fixed-point equation (7) of Theorem 1 into an integral equation for the payoff function of the optimal claim on $X$, which is the form used to compute the hedge numerically (Theorem EC.1).
--
--   **Formalization Note** $L^2_X$ is $L^2$ of the law $\mathbb P_X$ of $X$. The Fredholm equation is asserted $\mathbb P_X$-almost everywhere, since $H^*_0(x)$ is an $L^2_X$ class and the ratios are undefined where $f_X=0$. Integrals are Bochner integrals and divisions are total ($t/0=0$), conventions that only act on null sets.
--
--   Differences from the source:
--   - correction: the second summand of (9) is printed as $\int\pi(\xi,y)f_{XI}(\xi,i)f_{XYI}(x,y,i)/(f_X(x)f_I(i))$ → Lean uses $\int\pi(\xi,y)f_{XYI}(\xi,y,i)f_{XI}(x,i)/(f_X(x)f_I(i))$; reason: the proof (p. ec25) derives (9) by inserting density forms of the conditional expectations into $\Pi^X_0=-\mathbb E[\mathcal K-\mathbb E[\mathcal K\mid\mathcal F_I]\mid\mathcal F_X]$, which gives the corrected pattern, and (EC.30) is printed in that pattern; the printed term is wrong: for $X,Z,I$ i.i.d. $N(0,1)$, $Y=X+Z$, $\pi(x,y)=y$, it equals $\mathbb E[Y\mid X=x]=x$ while $\mathbb E[\mathbb E[\pi\mid\mathcal F_I]\mid X=x]=\mathbb E[Y]=0$.
--   - reading: "$(x\in\mathbb R^N)$" in (8) and "$G^*(x)=G^*_0(x)-c^*_G$" → (8) holds for $\mathbb P_X$-a.e. $x$, and $G^*$ is a payoff function of $i$; reason: $H^*_0$ is an element of $L^2_X$ and the ratios are undefined off the support of $f_X$; $G^*$ is a claim on $I$.
--   - reading: "the optimal combined custom hedge exhibits payoff functions" → for every optimal pair of (4) there exist Borel payoff functions representing $H^*_0,G^*_0$ a.s.; reason: the optimal pair is unique only a.s. (Theorem 1), so payoff functions exist up to null sets.
--   - encoding: $f^{\mathbb Q}_X,f^{\mathbb Q}_I$ used without definition → hypotheses that they are densities of the $\mathbb Q$-laws of $X$ and $I$; reason: they exist because $\mathbb Q\ll\mathbb P$ and are unique a.e., so the statement does not depend on the version.
--   - encoding: $a\ge0$ → $a>0$ (base standing assumptions); reason: $\mathcal K$ and (9) divide by $a$; this inherits the base mission's added assumption and excludes the source's $a=0$ case.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. 12 (PDF 12), Theorem 2, (8), (9); proof pp. ec25–ec26 (PDF 56–57), EC.3.3, (EC.29), (EC.30)

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model
import Definitions.Def_CustomHedge_Exist_Supplement_Densities

namespace CustomHedge.Exist.Supplement

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

/-- Theorem 2 (p. 12). Let `X, Y, I` be `ℝ^N`-valued with a joint `P`-density `f_XYI`, let
`f^Q_X, f^Q_I` be densities of the laws of `X` and `I` under `Q`, and let `r_XI < 1`. For every
optimal pair `(H*, G*)` of problem (4), with `H*₀ = H* - E[H*]`, `G*₀ = G* - E[G*]`, there are
Borel payoff functions `H*₀(x) ∈ L²_X`, `G*₀(i) ∈ L²_I` with `H*₀ = H*₀(X)`, `G*₀ = G*₀(I)`,
`H* = H*₀(X) - c*_H`, `G* = G*₀(I) - c*_G` (`c*_H = E_Q[H*₀(X)]`, `c*_G = E_Q[G*₀(I)]`), and
`H*₀(x) = Π^X_0(x) + ∫ k(x, ξ) H*₀(ξ) dξ` for `L_P(X)`-a.e. `x` (the Fredholm equation (8)). -/
theorem theorem_2 (M : Market Ω (Rn N) (Rn N) (Rn N)) (hS : M.Standing)
    (f : Rn N → Rn N → Rn N → ℝ) (hf : IsJointDensity M f)
    (fQX fQI : Rn N → ℝ) (hQX : IsLawDensity (Qmeas M) M.X fQX)
    (hQI : IsLawDensity (Qmeas M) M.I fQI)
    (hr : M.maxCorr < 1) (H G : Ω → ℝ) (hopt : M.IsOptimal H G) :
    ∃ h₀ g₀ : Rn N → ℝ, Measurable h₀ ∧ Measurable g₀ ∧
      MemLp h₀ 2 (M.P.map M.X) ∧ MemLp g₀ 2 (M.P.map M.I) ∧
      (fun ω => H ω - ∫ ω', H ω' ∂M.P) =ᵐ[M.P] (fun ω => h₀ (M.X ω)) ∧
      (fun ω => G ω - ∫ ω', G ω' ∂M.P) =ᵐ[M.P] (fun ω => g₀ (M.I ω)) ∧
      H =ᵐ[M.P] (fun ω => h₀ (M.X ω) - M.EQ (fun ω' => h₀ (M.X ω'))) ∧
      G =ᵐ[M.P] (fun ω => g₀ (M.I ω) - M.EQ (fun ω' => g₀ (M.I ω'))) ∧
      ∀ᵐ x ∂(M.P.map M.X),
        h₀ x = Pi0Xfun M f fQX fQI x + ∫ ξ, kernel f x ξ * h₀ ξ := by sorry

end CustomHedge.Exist.Supplement
