-- Prove2me | Theorems.Thm_ConformalRiskControl_tv_bound_distribution_shift
-- name    : ConformalRiskControl.tv_bound_distribution_shift
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:16:59.85141+00:00
-- url     : https://prove2.me/theorems/4ac67a7b-8358-4d05-a3b1-34e02382a269
-- title:
--   Proposition 3 (as proved): total variation bound under distribution shift
-- statement:
--   Let $Z_1,\dots,Z_{n+1}$ be independent random elements of a measurable space $\mathcal Z$, $n\ge1$. Let $\Lambda\subset\mathbb{R}$ be nonempty and compact, and $\alpha<B$. Let $\ell:\mathcal Z\times\Lambda\to\mathbb{R}$ be measurable in $z$ for each $\lambda$, and non-increasing and right-continuous in $\lambda$ for each $z$. Assume that almost surely, for every $i$, $\ell(Z_i,\cdot)$ takes values in $[0,B]$ and $\ell(Z_i,\lambda_{\max})\le\alpha$. Let $\hat\lambda$ be the parameter of eq. (4) for $L_i=\ell(Z_i,\cdot)$. Then
--   $$\mathbb{E}\big[L_{n+1}(\hat\lambda)\big]\le\alpha+B\sum_{i=1}^n\mathrm{TV}(Z_i,Z_{n+1}).$$
--   Suppose further that $\Lambda=[a,b]$ with $a<b$, that $\mathbb{P}(J(\ell(Z_{n+1},\cdot),\lambda)>0)=0$ for every $\lambda\in(a,b]$, and that $\ell(Z_{n+1},a)\ge\alpha$ almost surely. Then
--   $$\mathbb{E}\big[L_{n+1}(\hat\lambda)\big]\ge\alpha-B\Big(\frac2{n+1}+\sum_{i=1}^n\mathrm{TV}(Z_i,Z_{n+1})\Big).$$
--
--   **Formalization Note** The printed statement allows an arbitrary sequence $Z$ and the losses of Theorem 1, which may be negative. The proof needs independence of the $Z_i$ and $0\le\ell\le B$, and the statement is false without either:
--
--   1. Let $n=1$, $B=1$, $\alpha=1/2$, $\ell(z,\lambda)=\mathbb{1}\{\lambda<z\}$ on $[0,1]$, and let $(Z_1,Z_2)$ be uniform on $\{(0,\tfrac12),(\tfrac12,1),(1,0)\}$. Then $\mathrm{TV}(Z_1,Z_2)=0$, but the risk is $2/3$.
--   2. Independent $Z_i$ with $\alpha=-1<0$ give risk $-1+2\epsilon>-1+\epsilon=\alpha+B\,\mathrm{TV}$.
--
--   For the lower bound, "the assumptions of Theorem 2" are read as they are used in the proof: for the law of $Z_{n+1}$, applied to i.i.d. copies of $Z_{n+1}$. They include the left-endpoint condition of Theorem 2 (as proved).
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Section 4.1, Proposition 3, pp. 10-11; proof in Appendix B, p. 18

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem tv_bound_distribution_shift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Type*} [MeasurableSpace Z] (n : ℕ) (hn : 0 < n)
    (Zs : Fin (n + 1) → Ω → Z) (hZ : ∀ i, Measurable (Zs i)) (hind : iIndepFun Zs P)
    (Λ : Set ℝ) (hΛ : IsCompact Λ) (hΛne : Λ.Nonempty) (B α : ℝ) (hαB : α < B)
    (ℓ : Z → ℝ → ℝ) (hℓ : ∀ x ∈ Λ, Measurable fun z => ℓ z x)
    (hanti : ∀ z, AntitoneOn (ℓ z) Λ) (hrc : ∀ z, IsRightContOn Λ (ℓ z))
    (hbd : ∀ᵐ ω ∂P, ∀ i, LossBounds Λ B α (ℓ (Zs i ω)) ∧ ∀ x ∈ Λ, 0 ≤ ℓ (Zs i ω) x) :
    upperExp P B (fun ω =>
        ℓ (Zs (Fin.last n) ω) (lhat Λ B α (fun i : Fin n => ℓ (Zs i.castSucc ω)))) ≤
      ((α + B * ∑ i : Fin n, tvDist (P.map (Zs i.castSucc)) (P.map (Zs (Fin.last n))) : ℝ)
        : EReal) ∧
    ∀ a b : ℝ, a < b → Λ = Set.Icc a b →
      (∀ x ∈ Set.Ioc a b, P {ω | 0 < jump (ℓ (Zs (Fin.last n) ω)) x} = 0) →
      (∀ᵐ ω ∂P, α ≤ ℓ (Zs (Fin.last n) ω) a) →
      ((α - B * (2 / (n + 1) +
          ∑ i : Fin n, tvDist (P.map (Zs i.castSucc)) (P.map (Zs (Fin.last n)))) : ℝ) : EReal) ≤
        upperExp P B (fun ω =>
          ℓ (Zs (Fin.last n) ω) (lhat Λ B α (fun i : Fin n => ℓ (Zs i.castSucc ω)))) := by sorry

end ConformalRiskControl
