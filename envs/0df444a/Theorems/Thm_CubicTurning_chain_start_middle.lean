-- Prove2me | Theorems.Thm_CubicTurning_chain_start_middle
-- name    : CubicTurning.chain_start_middle
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:36:36.91036+00:00
-- url     : https://prove2.me/theorems/e92bd755-9d7f-4534-8af8-a9855825c154
-- title:
--   Normalized cubic chains start at zero and use critical points ±1
-- statement:
--   For complex $a,b,c$ put $P_{a,b,c}(X)=(X-a)(X-b)(X-c)$. A length-three chain $z=(z_0,z_1,z_2)$ means precisely $P_{a,b,c}^{\prime\prime}(z_0)=0$, $P_{a,b,c}^{\prime}(z_1)=0$, and $P_{a,b,c}(z_2)=0$. Being forward for an axis $e$ and consecutive displacements $d_0=z_1-z_0$, $d_1=z_2-z_1$ means $|e|=1$, $\operatorname{Re}(ed_0)\ge0$, and $\operatorname{Re}(ed_1)\ge0$; zero displacements and zero projections are allowed. For all complex $a,b,c$, if $a+b+c=0$ and $a^2+b^2+c^2=6$ as complex equalities, then every length-three chain $z$ for this triple satisfies $z_0=0$ and $(z_1=1\text{ or }z_1=-1)$. There is no forwardness or chosen-endpoint hypothesis. The middle alternatives are an inclusive disjunction in the statement, and the conclusion adds no relation selecting one according to $z_2$. Repeated roots are not excluded.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSharpness.lean, lines 94-111, SHA-256 387285b9af69f97f92225f56b89ed0b82ae043d24968cf05a356099163011707. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.chain_start_middle (a b c : ℂ) (hcenter : a+b+c=0)
    (hsecond : a^2+b^2+c^2=6) (z : Fin 3 → ℂ)
    (hz : DerivativeChainPrivate.IsChain ![a,b,c] z) :
    z 0=0 ∧ (z 1=1 ∨ z 1=-1) := by sorry
