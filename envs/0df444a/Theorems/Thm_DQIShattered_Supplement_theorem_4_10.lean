-- Prove2me | Theorems.Thm_DQIShattered_Supplement_theorem_4_10
-- name    : DQIShattered.Supplement.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:37:41.259624+00:00
-- url     : https://prove2.me/theorems/1f7a12b1-81c7-4c88-8e52-528679083d1f
-- title:
--   Theorem 4.10 — Shattering forces exponentially slow Glauber mixing
-- statement:
--   Fix $\varepsilon\in(0,1/2)$, an integer $k\ge2$, a real $D>0$, and an inverse temperature $\beta$. If the Gibbs measure of $H\sim\mathbb G_{\mathrm{ER}}(N,k,D)$ is $\varepsilon$-shattered with high probability, then there is an $a>0$, independent of $N$, such that the random-scan single-site heat-bath Glauber dynamics for $\mu_{\beta,H}$ has worst-start total-variation mixing time at least
--   $$
--   e^{aN}
--   $$
--   with probability tending to one.
--
--   Differences from the source:
--   - encoding: mixing time $e^{\Omega(N)}$ → Lean quantifies a fixed $a>0$ and requires that before every integer time $t<e^{aN}$ some initial state remains at total variation distance greater than $1/4$; reason: this is the standard worst-start total-variation definition and avoids a default-valued infimum
--   - encoding: $H\sim\mathbb G_{\mathrm{ER}}(N,k,D)$ → Lean makes the ensemble's standing assumptions $k\ge2$ and $D>0$ explicit; reason: these are Definition 2.5's domain, not additional restrictions
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 4.10, pp.21–22

import Mathlib
import Definitions.Def_DQIShattered_Supplement_Framework

namespace DQIShattered

namespace Supplement

/-- **Theorem 4.10.**
Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…,
p.21.

For every `ε ∈ (0,1/2)`, if the random Max-`k`-XORSAT Gibbs measures are `ε`-shattered with
high probability in the exact sense of Definition 4.4, then their random-scan single-site
heat-bath Glauber chains have worst-start total-variation mixing time at least `exp(aN)` with
high probability, for one positive rate `a` independent of `N`. -/
theorem theorem_4_10 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (k : ℕ) (hk : 2 ≤ k) (D β : ℝ) (hD : 0 < D)
    (hshatter : IsShattered k D β ε) :
    ExponentialGlauberMixing k D β := by sorry

end Supplement

end DQIShattered
