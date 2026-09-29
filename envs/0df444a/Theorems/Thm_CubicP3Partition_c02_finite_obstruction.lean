-- Prove2me | Theorems.Thm_CubicP3Partition_c02_finite_obstruction
-- name    : CubicP3Partition.c02_finite_obstruction
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T03:07:33.138712+00:00
-- url     : https://prove2.me/theorems/208ec141-9f72-4417-aea6-3fa6963fe652
-- title:
--   C02: the 18-vertex route obstruction
-- statement:
--   For the explicitly defined graph $H_0$ on 18 vertices, all four assertions hold:
--
--   1. $H_0$ is cubic;
--   2. $H_0$ is 3-vertex-connected;
--   3. $H_0$ has a noninduced $P_3$-factor;
--   4. no perfect matching of $H_0$ has a complementary 2-factor whose every component order is divisible by three.
--
--   $$
--   \operatorname{Cubic}(H_0)\land\operatorname{ThreeVertexConnected}(H_0)\land
--   \operatorname{Nonempty}(\operatorname{P3Factor}(H_0))\land
--   \neg\operatorname{HasDivisibleComplement}(H_0).
--   $$
--
--   This is a boundary result for a stronger sufficient route, not a counterexample to the main open problem. The cited repository currently classifies it as candidate-only; this theorem is the outstanding kernel-check target.
-- source:
--   Vibe Mathing C02, https://github.com/vibemathing/problem-opg-46613-cubic-p3-partition/blob/14b8dc64ac2d89c98cf3a2bbb2fcba76ced0df6a/research/artifacts/candidates/opg46613-c02/proof.md, Sections C02.3–C02.4; independent verifier report at https://github.com/vibemathing/problem-opg-46613-cubic-p3-partition/blob/14b8dc64ac2d89c98cf3a2bbb2fcba76ced0df6a/research/artifacts/candidates/opg46613-c08-independent-verifier/verifier-report.md; fixed revision 14b8dc64ac2d89c98cf3a2bbb2fcba76ced0df6a.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

/-- The 18-vertex member of the C02 candidate family. -/
theorem c02_finite_obstruction :
    Cubic (H 0) ∧ ThreeVertexConnected (H 0) ∧
      Nonempty (P3Factor (H 0)) ∧ ¬ HasDivisibleComplement (H 0) := by sorry

end CubicP3Partition
