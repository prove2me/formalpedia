-- Prove2me | Theorems.Thm_CritWinSpin_Implementation_SamplerRuntime_criticalWindowMachine_time
-- name    : CritWinSpin.Implementation.SamplerRuntime.criticalWindowMachine_time
-- status  : Proved
-- author  : @Maxliu
-- created : 2026-11-17T18:23:57.39925+00:00
-- url     : https://prove2.me/theorems/d8b0aa69-2026-447f-ab41-6ad20191e1e7
-- title:
--   Theorem 4.4 — running time of the finite sampler
-- statement:
--   Let $S$ be a GHS spin law of type $p$, and choose the numerical scale $C$ to satisfy the stated scale and integration bounds. The concrete sampler $M_{S,C}$ has constants $C_{\mathrm{time}}>0$ and $k\in\mathbb N$ such that, for every rational instance with
--
--   $$0\preceq J\preceq\tau_S(1+\delta)I_N,\qquad \delta\ge0,\quad m\ge5,$$
--
--   its running time is at most
--
--   $$C_{\mathrm{time}}(N+B+m)^k\exp\!\left(C_{\mathrm{time}}N\delta^{p/(p-1)}\right).$$
--
--   Here $B$ is the encoded instance length. The machine and the constants are fixed before $N,J,h,m,\delta$. This is the running-time part of the sampler construction in Theorem 4.4.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 4.4, p.17, equation (24). Running-time component of the concrete sampler.

import Definitions.Def_CritWinSpin_SamplerMachine
import Definitions.Def_CritWinSpin_encInst
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC
open CritWinSpin CritWinSpin.LocalTM2.Compiled
open CritWinSpin.Implementation.PreprocessIntegral
set_option autoImplicit false

namespace CritWinSpin.Implementation.SamplerRuntime

theorem criticalWindowMachine_time (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (C : ℕ) (hC8 : 8 ≤ C) (hC : 1000 * (fixedScale S : ℝ) ≤ (C : ℝ))
    (hPrecision : 1000 * integrationConstant S ≤ (C : ℝ)) :
    ∃ (Ctime : ℝ) (k : ℕ), 0 < Ctime ∧ ∀ (N : ℕ) (I : Inst N) (m : ℕ) (δ : ℝ),
      I.1.IsSymm → (castM I.1).PosSemidef → 0 ≤ δ →
      ((tau S*(1+δ)) • (1 : Matrix (Fin N) (Fin N) ℝ)-castM I.1).PosSemidef → 5 ≤ m →
      ((criticalWindowMachine S C).time (tupleCode [encInst I, encBin m]) : ℝ) ≤
        Ctime * ((N : ℝ) + bitLen I + m) ^ k *
          Real.exp (Ctime * N * δ ^ ((p : ℝ) / ((p : ℝ)-1))) := by sorry

end CritWinSpin.Implementation.SamplerRuntime
