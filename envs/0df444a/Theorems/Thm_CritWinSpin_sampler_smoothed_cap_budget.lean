-- Prove2me | Theorems.Thm_CritWinSpin_sampler_smoothed_cap_budget
-- name    : CritWinSpin.sampler_smoothed_cap_budget
-- status  : Proved
-- author  : @Maxliu
-- created : 2026-11-17T11:27:00.009211+00:00
-- url     : https://prove2.me/theorems/b0c1244a-109c-463b-8c90-c73dffdaf31e
-- title:
--   平滑谱余量下的凸包预算 N∆s+1 ≤ D(Nδ^{p/(p−1)}+1)
-- statement:
--   设 $\rho$ 为 GHS 单点分布且具有熵阶 $p\ge2$，$\tau$ 为其临界阈值，$\Delta_s$ 为 Lemma 4.2 的凸包损失。存在仅依赖 $\rho,p$ 的常数 $D>0$，对每个维数 $N\ge0$、整数精度参数 $m\ge5$ 以及谱超临界量 $\delta\ge0$，令
--   $$s=\tau(1+\delta)+\frac1{m(N+1)}.$$
--   则
--   $$N\Delta_s+1\le D\bigl(N\delta^{p/(p-1)}+1\bigr).$$
--   这把有限精度 sampler 为谱估计和矩阵分解保留的正余量吸收到固定常数中，给出 Theorem 4.4 从凸包损失时间界转为临界窗口时间界所需的统一预算。量词包含临界点 $\delta=0$ 及空系统 $N=0$。
--
--   **Formalization Note** 原文取 $e=1/(8mN)$；这里使用有定义的余量 $1/[m(N+1)]$。它同样满足 $Ne^{p/(p-1)}\le1$，因此得到同一个统一指数界。
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission, manuscript SHA256 f77584dab87d9e6d0936a083a2e3d26476a91a9d73dc303674514a3257c0de95, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/943.pdf, Lemma 4.2(ii), eq. (22), printed pp.14–15; Theorem 4.4 proof, printed p.17, displayed K=N∆s=Oρ(Nδ^{p/(p−1)}+1). The statement uses a slightly different O(1/[m(N+1)]) safety margin and includes N=0.

import Mathlib
import Definitions.Def_CritWinSpin_Wpot
open CritWinSpin
set_option autoImplicit false

theorem CritWinSpin.sampler_smoothed_cap_budget (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N m : ℕ) (δ : ℝ), 5 ≤ m → 0 ≤ δ →
      (N : ℝ) * deltaS S
          (tau S * (1 + δ) + 1 / ((m : ℝ) * ((N : ℝ) + 1))) + 1 ≤
        D * ((N : ℝ) * δ ^ ((p : ℝ) / ((p : ℝ) - 1)) + 1) := by sorry
