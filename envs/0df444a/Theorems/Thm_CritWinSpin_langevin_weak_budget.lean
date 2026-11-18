-- Prove2me | Theorems.Thm_CritWinSpin_langevin_weak_budget
-- name    : CritWinSpin.langevin_weak_budget
-- status  : Proved
-- author  : @Maxliu
-- created : 2026-11-17T16:58:13.319194+00:00
-- url     : https://prove2.me/theorems/eec40877-e16c-49e4-b8f7-326041966f7b
-- title:
--   Langevin iteration with finite precision: explicit weak-error budget
-- statement:
--   设 $E=\mathbb R^d$ 带欧氏范数，$U:E\to\mathbb R$ 为连续势函数，$\mu$ 是密度正比于 $e^{-U}$ 的概率测度，$g:E\to E$ 为连续漂移。假定 $g$ 以常数 $a>0$ 强单调、Lipschitz 常数至多为 $4$，且 $|U(y)-U(x)-\langle y-x,g(x)\rangle|\le\|y-x\|^2$。记 $c_6=\mathbb E|Z|^6$，其中 $Z$ 为一维标准高斯。
--
--   令 $Q$ 作用于有界可测测试函数，保持可测性和一致界，并在一致范数中不扩张。对于任意有界 $L$-Lipschitz 测试函数，假设 $Q$ 与高斯 Euler 步 $x\mapsto x-s^2g(x)+\sqrt2sG$ 的单步期望差至多为 $Le$。
--
--   取 $R\ge2$，要求 $aR\ge1$、$\mathbb E_\mu\|X\|\le R$、$2+\mathbb E_\mu\|g(X)\|^6+c_6d^3\le R$，并要求这些矩确有可积性。若 $0<s\le1$、$e\ge0$、$as^2\le1$、$16s^2\le a$，且
--
--   $$s\le\frac1{2048R^4},\qquad e\le\frac{s^2}{16R^3},\qquad n\ge\frac{16R^4}{s^2},$$
--
--   则每个有界、可测且 $0\le L\le R$ 的 Lipschitz 测试函数满足
--
--   $$\left|Q^nf(0)-\mathbb E_\mu f\right|\le\frac1{2R}.$$
--
--   这是 Theorem 4.4 有限精度采样器所用的通用 Langevin 弱误差估计。它把势函数的几何条件、两个矩界与实际数值算子的单步误差合并成显式的有限步精度保证。
-- source:
--   New auxiliary finite-dimensional weak-approximation theorem supporting Theorem 4.4, section4.2, pp16-17, of The Critical Window for Sampling and Learning-to-Sample in Spin Systems. Official manuscript https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/943.pdf (SHA256 f77584dab87d9e6d0936a083a2e3d26476a91a9d73dc303674514a3257c0de95). The explicit R-budget statement and Metropolis-flux proof are new formal support results, not a separately numbered lemma in that manuscript.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace CritWinSpin

theorem langevin_weak_budget (d : ℕ) (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (hμ : μ = ((∫⁻ x : EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal (Real.exp (-U x)) ∂volume)⁻¹) •
      (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (a s e R : ℝ)
    (hU : Continuous U) (hg : Continuous g)
    (hiU : Integrable (fun x => Real.exp (-U x)))
    (hmono : ∀ x y, a * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) (g x - g y))
    (hTaylor : ∀ x y, |U y - U x - inner ℝ (y - x) (g x)| ≤ ‖y - x‖ ^ 2)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ 4 * ‖x - y‖)
    (hiG : Integrable (fun x => ‖g x‖ ^ 6) μ)
    (hiNorm : Integrable (fun x => ‖x‖) μ)
    (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1) (he0 : 0 ≤ e)
    (hsmall : a * s ^ 2 ≤ 1) (hstep : 16 * s ^ 2 ≤ a)
    (hR : 2 ≤ R) (haR : 1 ≤ a * R) (hsR : s ≤ 1 / (2048 * R ^ 4))
    (he : e ≤ s ^ 2 / (16 * R ^ 3))
    (hM : (∫ x, ‖x‖ ∂μ) ≤ R)
    (hH : 2 + (∫ x, ‖g x‖ ^ 6 ∂μ) +
      (∫ t : ℝ, |t| ^ 6 ∂gaussianReal 0 1) * (d : ℝ) ^ 3 ≤ R)
    (Q : (EuclideanSpace ℝ (Fin d) → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ)
    (hQ : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (B : ℝ),
      Measurable f → (∀ x, |f x| ≤ B) → Measurable (Q f) ∧ ∀ x, |Q f x| ≤ B)
    (hQC : ∀ (f k : EuclideanSpace ℝ (Fin d) → ℝ) (B D : ℝ),
      Measurable f → Measurable k → (∀ x, |f x| ≤ B) → (∀ x, |k x| ≤ B) →
      (∀ x, |f x - k x| ≤ D) → ∀ x, |Q f x - Q k x| ≤ D)
    (happrox : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (B L : ℝ), 0 ≤ L →
      Measurable f → (∀ x, |f x| ≤ B) → (∀ x y, |f x - f y| ≤ L * dist x y) →
      ∀ x, |Q f x - ∫ z, f (x - s ^ 2 • g x + (Real.sqrt 2 * s) • z)
        ∂stdGaussian (EuclideanSpace ℝ (Fin d))| ≤ L * e)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (B L : ℝ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hf : Measurable f)
    (hfB : ∀ x, |f x| ≤ B) (hfL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (n : ℕ) (hn : 16 * R ^ 4 / s ^ 2 ≤ (n : ℝ)) :
    |(Q^[n] f) 0 - ∫ x, f x ∂μ| ≤ 1 / (2 * R) := by sorry

end CritWinSpin
