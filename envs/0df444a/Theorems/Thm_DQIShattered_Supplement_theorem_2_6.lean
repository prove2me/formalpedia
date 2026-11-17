-- Prove2me | Theorems.Thm_DQIShattered_Supplement_theorem_2_6
-- name    : DQIShattered.Supplement.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:34:26.078167+00:00
-- url     : https://prove2.me/theorems/a21366c1-f263-4835-9f8e-4870b95a75c4
-- title:
--   Theorem 2.6 — Shattering and failure of stable samplers
-- statement:
--   For every fixed $\varepsilon>0$, there is $k_0(\varepsilon)\ge3$ such that for every fixed integer $k\ge k_0(\varepsilon)$, every fixed real $D\ge k$, and every
--   $$
--   (1+\varepsilon)\sqrt{\frac{2\ln k}{D}}\le\beta\le\sqrt{\frac{k}{2D}},
--   $$
--   the Gibbs measure of $H\sim\mathbb G_{\mathrm{ER}}(N,k,D)$ is $(\varepsilon/k)$-shattered with exponentially good probability as $N\to\infty$. In the same interval there is an $N$-independent $\iota_*>0$ such that every $\iota$-stable sampler family with $0<\iota\le\iota_*$ has strictly positive asymptotic expected normalized-Wasserstein error, and there is an $a>0$ for which single-site Glauber dynamics has worst-start total-variation mixing time at least $e^{aN}$ with high probability.
--
--   This is the paper's joint hardness theorem: shattering obstructs stable sampling and creates an exponential bottleneck for local Markov-chain sampling.
--
--   Differences from the source:
--   - generalization: the theorem says that the Gibbs measure shatters into exponentially many well-separated clusters with high probability → Lean states the stronger $(\varepsilon/k)$-shattering conclusion with an explicit exponentially-good probability bound; reason: Theorem 4.6 and Propositions 5.9–5.11 prove this stronger quantitative form
--   - encoding: no stable algorithm can sample with vanishing expected normalized Wasserstein distance → Lean exposes the fixed $N$-independent constant $\iota_*>0$ and a strictly positive liminf error; reason: this is the quantitative statement of Theorem 4.3
--   - encoding: Glauber dynamics has $e^{\Omega(N)}$ mixing time with high probability → Lean quantifies a fixed rate $a>0$ and uses the standard worst-start total-variation threshold $1/4$; reason: this is the usual meaning of the displayed asymptotic claim
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 2.6, p.6, eq. (2.8)

import Mathlib
import Definitions.Def_DQIShattered_Supplement_Framework

namespace DQIShattered

namespace Supplement

/-- **Theorem 2.6 (Shattering and failure of stable samplers).**
Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum
Interferometry*, arXiv:2609.40345, held version sha256 0c7f6fdf…, p.6.

For every fixed positive `ε`, all sufficiently large fixed `k`, every fixed real `D ≥ k`, and
every inverse temperature in (2.8), the random Max-`k`-XORSAT Gibbs law is `(ε/k)`-shattered
with exponentially good probability, every sufficiently stable distribution-valued sampler has
nonvanishing expected normalized-Wasserstein error, and single-site Glauber dynamics has
exponential worst-start total-variation mixing time with high probability.

**Formalization Note** The `(ε/k)` shattering parameter is the stronger reading proved in
Theorem 4.6. 'Exponentially good' retains the positive constant furnished by Propositions
5.9–5.11. `StableObstruction` expands the paper's fixed, `N`-independent `ι_*`; and
`ExponentialGlauberMixing` expands `e^{Ω(N)}` using a fixed positive rate. -/
theorem theorem_2_6 :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ D : ℝ, (k : ℝ) ≤ D → ∀ β : ℝ, InHardRange k D ε β →
        IsExponentiallyShattered k D β (ε / k) ∧
          StableObstruction k D β ∧ ExponentialGlauberMixing k D β := by sorry

end Supplement

end DQIShattered
