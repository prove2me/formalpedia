-- Prove2me | Theorems.Thm_CubicTurning_central_history_forces_energy_negative
-- name    : CubicTurning.central_history_forces_energy_negative
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:34:35.43236+00:00
-- url     : https://prove2.me/theorems/4a3a6e9e-4a5c-42ef-835d-b776404df474
-- title:
--   The other critical point has the same forced central energy
-- statement:
--   For $e,d_0,d_1\in\mathbb C$, use Euclidean modulus $|z|=\sqrt{(\operatorname{Re}z)^2+(\operatorname{Im}z)^2}$ and set $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$, with real division by zero defined to be $0$. Let $T(e,d_0,d_1)$ mean $(h(e,d_0)\ge1/7\ \text{and}\ h(e,d_1)\le-1/7)$ or the same two inequalities with $d_0,d_1$ exchanged. Put $B(d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$, $E(e,d_0,d_1)=B(d_0,d_1)$ if $T$ holds and $0$ otherwise, and $A(e,d_0,d_1)=(|d_0|+\operatorname{Re}(ed_0))(|d_1|+\operatorname{Re}(ed_1))(h(e,d_0)-h(e,d_1))^2$ if $T$ holds and $0$ otherwise. Every threshold inequality is non-strict. For every real $t$ with $0<t\le1$ and every complex $e$ satisfying $|e|=1$, $\operatorname{Re}(e(-1))\ge0$, and $\operatorname{Re}(e(1+\mathrm i t))\ge0$, $E(e,-1,1+\mathrm i t)=2+2\sqrt{1+t^2}$. The equality applies to every such axis, includes $t=1$, and excludes $t=0$.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSharpness.lean, lines 79-92, SHA-256 387285b9af69f97f92225f56b89ed0b82ae043d24968cf05a356099163011707. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.central_history_forces_energy_negative (t : ℝ) (e : ℂ) (ht : 0<t) (ht1 : t≤1)
    (hf : IsForward e (-1:ℂ) (1+Complex.I*(t:ℂ))) :
    energy e (-1:ℂ) (1+Complex.I*(t:ℂ))=2+2*Real.sqrt (1+t^2) := by sorry
