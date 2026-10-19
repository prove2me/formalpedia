-- Prove2me | Theorems.Thm_DelegStop_Commit_expected_quality
-- name    : DelegStop.Commit.expected_quality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:09.759636+00:00
-- url     : https://prove2.me/theorems/9d3d7607-7277-4f2c-acc8-de6c294f78f6
-- title:
--   §3.2 property (2), p. 6322 (PDF 7) — the expected solution quality under effort μ is kμ
-- statement:
--   Let $k > 0$ and $0 \le \mu \le 1$, and let the solution quality $v$ have the distribution $\Phi_\mu(x) = 1 - \mu e^{-x/k}$ of §3.2: an atom of mass $1-\mu$ at $0$ and density $\frac{\mu}{k}e^{-v/k}$ on $(0,\infty)$. Then the expected quality is $k\mu$:
--   $$\int_0^\infty v \cdot \frac{\mu}{k} e^{-v/k}\, dv = k\mu .$$
--
--   This is property (2) of the quality law in §3.2. It identifies $k$ as the provider's capability (the mean quality per unit of effort) and is the basic computation behind every closed-form value in the two-round game.
--
--   **Formalization Note.** The atom at $0$ contributes $0 \cdot (1-\mu) = 0$ to the mean, so the expectation is the integral of $v$ against the density over the open ray $(0,\infty)$. Only the equality is stated; the monotonicity in $\mu$ and $k$ that the page mentions is immediate from it.
-- source:
--   Rahmani & Ramachandran, Delegating Innovation Projects with Deadline: Committed vs. Flexible Stopping, Management Science 67(10):6317–6332 (2021), p. 6322 (PDF 7), §3.2, property (2)

import Mathlib
import Definitions.Def_DelegStop_Commit_Model

namespace DelegStop.Commit

theorem expected_quality (μ k : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hk : 0 < k) :
    ∫ v in Set.Ioi 0, v * qualDensity μ k v = k * μ := by sorry

end DelegStop.Commit
