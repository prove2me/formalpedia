-- Prove2me | Theorems.Thm_CubicTurning_energy_eq_halfAngleEnergy
-- name    : CubicTurning.energy_eq_halfAngleEnergy
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:38:45.066079+00:00
-- url     : https://prove2.me/theorems/db32f78f-34ad-400b-8a30-1c0d87bd728a
-- title:
--   Pair energy equals the original weighted half-angle expression
-- statement:
--   For complex $e,d_0,d_1$, set $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$, using the total real division convention that division by zero is $0$. Let $T(e,d_0,d_1)$ mean $[h(e,d_0)\ge 1/7\text{ and }h(e,d_1)\le-1/7]$ or the same two inequalities with $d_0,d_1$ exchanged. Define $E(e,d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$ when $T$ holds, and $E=0$ otherwise. All threshold inequalities are non-strict, and all complex moduli are Euclidean. For every complex $e,d_0,d_1$ satisfying $|e|=1$, $\operatorname{Re}(ed_0)\ge0$, and $\operatorname{Re}(ed_1)\ge0$, $E(e,d_0,d_1)$ equals $(|d_0|+\operatorname{Re}(ed_0))(|d_1|+\operatorname{Re}(ed_1))(h(e,d_0)-h(e,d_1))^2$ when $T$ holds, and zero otherwise. Zero displacements are included and give zero on both sides; no strict projection or separate denominator hypothesis is made.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 315-343, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.energy_eq_halfAngleEnergy (e d₀ d₁ : ℂ) (hf : IsForward e d₀ d₁) :
    energy e d₀ d₁=halfAngleEnergy e d₀ d₁ := by sorry
