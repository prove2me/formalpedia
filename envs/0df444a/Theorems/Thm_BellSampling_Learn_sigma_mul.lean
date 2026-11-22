-- Prove2me | Theorems.Thm_BellSampling_Learn_sigma_mul
-- name    : BellSampling.Learn.sigma_mul
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:45.401892+00:00
-- url     : https://prove2.me/theorems/2c5cbdab-fd42-491c-a137-830f03539e2e
-- title:
--   Preliminaries, p. 1 — up to a sign, σ_sσ_t = σ_{s⊕t}
-- statement:
--   For strings $s,t\in\{0,1\}^{2n}$, the product of the tensor-product matrices $\sigma_s$ and $\sigma_t$ is $\sigma_{s\oplus t}$ up to a sign:
--   $$\sigma_s\sigma_t=\sigma_{s\oplus t}\quad\text{or}\quad \sigma_s\sigma_t=-\sigma_{s\oplus t}.$$
--
--   This is the multiplication rule of the matrices $\sigma_s$; it makes the map $s\mapsto\sigma_s$ a homomorphism up to sign and underlies the identification of stabilizer groups with subspaces of $\mathbb F_2^{2n}$.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 1, Preliminaries, "Up to multiplying by −1, σsσt = σs⊕t."

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem sigma_mul {n : ℕ} (s t : PStr n) :
    sigma s * sigma t = sigma (s + t) ∨ sigma s * sigma t = -sigma (s + t) := by sorry
end BellSampling.Learn
