-- Prove2me | Theorems.Thm_CtrlVolMFG_lemma_3_13
-- name    : CtrlVolMFG.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:12.483985+00:00
-- url     : https://prove2.me/theorems/aa863199-e2e9-4913-b5cb-64b956e394b0
-- title:
--   Lemma 3.13 — weak error $\mathbb E|\mathcal U(x,m)-\mathcal U(x,m^N_\xi)|^2\le\frac CN(1+|x|^2+M_2(m))$
-- statement:
--   Let $E$ be a Euclidean space and $\mathcal U:E\times\mathcal P_2(\mathbb R^n)\to\mathbb R$ a function of linear growth such that for each fixed $x$ the map $m\mapsto\mathcal U(x,m)$ admits the derivatives $D_m\mathcal U(x,m,p)$ and $D_{mm}\mathcal U(x,m,p,q)$, bounded and Lipschitz continuous uniformly in $x$. Then there is a constant $C$, independent of $N$ and $m$, such that for any $N$ i.i.d. random variables $\xi^1,\dots,\xi^N$ with common law $m$ and every $x\in E$,
--   $$\mathbb E\big[|\mathcal U(x,m)-\mathcal U(x,m^N_{\boldsymbol\xi})|^2\big]\le\frac CN\big(1+|x|^2+M_2(m)\big),\qquad m^N_{\boldsymbol\xi}=\frac1N\sum_{i=1}^N\delta_{\xi^i}.$$
--
--   Applied conditionally on $\mathcal F^0_t$ to the copies, it bounds the error terms of Proposition 3.16 by $C/N$.
--
--   Differences from the source:
--   - reading: $D_{mm}D_x\mathcal U(x,m,p,q)=D_{mm}[D_x\mathcal U(x,\cdot)](m,p,q)$ → $D_{mm}\mathcal U(x,m,p,q)=D_{mm}[\mathcal U(x,\cdot)](m,p,q)$; reason: the proof (3.20) uses the second Lions derivative of $\mathcal U$ itself, and $\mathcal U$ is real valued
--   - reading: "of linear growth" → $|\mathcal U(x,m)|\le K(1+|x|+M_2(m)^{1/2})$; reason: the growth used in (3.21)
--   - reading: "bounded and Lipschitz in $m$, uniformly in $(x,y,z,z^0)$" (Assumption 2.20, Theorem 2.23 (2)) → one bound and one $\mathcal W_2$-Lipschitz constant in $m$, valid for all other arguments including the points $p,q$ (`TwoLionsUnif`); reason: the page asks Lipschitz continuity in $m$ uniformly in the remaining arguments
--   - encoding: "any $N$ i.i.d. random variables" → random variables on an arbitrary probability space (`Ω′ : Type`), measurable, independent (`iIndepFun`), each with law $m$; reason: same objects
--   - encoding: a Euclidean space $E$ → `EuclideanSpace ℝ (Fin p)`; reason: every Euclidean space is isometric to one of these
--   - encoding: §2.3: Fréchet differentiability of the lift $\xi\mapsto U(x,\mathcal L(\xi))$ on $\mathbb L^2(\Omega)$, with continuous $D_mU$ → the published `DisplMonoMFG.WellPosed.HasLDeriv` (first-order expansion uniform over the joint laws of $(\xi,\eta)$ with $\mathcal L(\xi)=m$), plus joint continuity; versions of $D_m$ as data (`Derivs`); reason: on an atomless space the two notions coincide; a Lions derivative is determined only $m$-a.e., and every statement evaluates it on the support
--   - encoding: $\mathbb E[\sup_t|\cdot|^2]$, $\mathbb E\int_0^T|\cdot|^2dt$ → lower Lebesgue integrals in $[0,\infty]$, bound $\mathrm{ofReal}(C/N)$; reason: same value; an infinite left side violates the bound in both
-- source:
--   Jackson & Tangpi, Quantitative Convergence for Displacement Monotone Mean Field Games with Controlled Volatility, arXiv:2304.04543v2, Lemma 3.13, p.27; (3.20)–(3.21) p.27

import Mathlib
import Definitions.Def_CtrlVolMFG_IsSol_3_6

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CtrlVolMFG

/-- Lemma 3.13 (Jackson & Tangpi, arXiv:2304.04543v2, p.27): let `E` be a Euclidean space and
`𝒰 : E × 𝒫₂(ℝⁿ) → ℝ` a function of linear growth such that for each fixed `x`, `m ↦ 𝒰(x, m)`
admits the derivatives `D_m𝒰(x, m, p)` and `D_mm𝒰(x, m, p, q)`, bounded and Lipschitz continuous,
uniformly in `x`. Then there is `C`, independent of `N` and `m`, such that for any `N` i.i.d.
random variables `(ξⁱ)` with common law `m` and every `x ∈ E`,
`𝔼[|𝒰(x, m) − 𝒰(x, m^N_ξ)|²] ≤ (C/N)(1 + |x|² + M₂(m))`, `m^N_ξ = (1/N) ∑ᵢ δ_{ξⁱ}`.

**Formalization Note** The page writes the second derivative as `D_mmD_x𝒰`; it is read as
`D_mm𝒰 = D_mm[𝒰(x, ·)]`, the derivative used in (3.20). Linear growth is
`|𝒰(x, m)| ≤ K(1 + |x| + M₂(m)^{1/2})`. The i.i.d. variables live on an arbitrary probability
space. -/
theorem lemma_3_13 {n p : ℕ} (U : EuclideanSpace ℝ (Fin p) → P2 n → ℝ)
    (hlin : ∃ K : ℝ, ∀ x m, |U x m| ≤ K * (1 + ‖x‖ + Real.sqrt (M2 m)))
    (hU : TwoLionsUnif U) :
    ∃ C : ℝ, ∀ N : ℕ, 0 < N → ∀ (m : P2 n) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (ξ : Fin N → Ω' → Rn n), (∀ i, Measurable (ξ i)) →
      iIndepFun ξ P' → (∀ i, P'.map (ξ i) = m.1) → ∀ x : EuclideanSpace ℝ (Fin p),
      ∫⁻ ω, ‖U x m - U x (empP2 fun i => ξ i ω)‖ₑ ^ 2 ∂P' ≤
        ENNReal.ofReal (C / N * (1 + ‖x‖ ^ 2 + M2 m)) := by sorry

end CtrlVolMFG
