-- Prove2me | Theorems.Thm_CosDensity_theorem_8_1_reduction
-- name    : CosDensity.theorem_8_1_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:23.817965+00:00
-- url     : https://prove2.me/theorems/1267d930-9f93-4b6b-ab8d-f7159767dc6e
-- title:
--   Proof of Theorem 8.1 — a streaming algorithm yields an $\mathrm{INDEX}_N$ protocol
-- statement:
--   Let $p\ge0$, $\epsilon\in\mathbb R$, let $\mathrm{pre}(z)$ ($z\in\{0,1\}^N$) and $\mathrm{suf}(q)$ ($q\in[N]$) be streams whose lengths $n_1$ and $n_2$ do not depend on $z$ and $q$, and let thresholds $\theta_q$ satisfy: for every $z,q$ and every $(1+\epsilon)$-approximation $Y$ of $M_p(\mathrm{pre}(z)\,\mathrm{suf}(q))$, $Y>\theta_q$ if and only if $z_q=1$.
--
--   Let $A$ be a randomized one-pass streaming algorithm with memory configurations $S$ and seed space $(\Omega,\mu)$ that outputs a $(1+\epsilon)$-approximation of $M_p$ with probability at least $2/3$ on every stream $\mathrm{pre}(z)\,\mathrm{suf}(q)$. Then there is a public-coin one-way protocol for $\mathrm{INDEX}_N$ with message set $S$ and the same seed space that errs with probability at most $1/3$ on every input pair.
--
--   Alice runs $A$ on her prefix and sends the memory configuration; Bob continues on his suffix and thresholds the estimate. Combined with Lemma 3.1 this turns the hard instances into a memory lower bound.
--
--   Differences from the source:
--   - generalization: the hard streams P(z, q) of (34), Alice's prefix and Bob's suffix → arbitrary prefix and suffix families of fixed lengths whose moments are separated by thresholds θ_q; reason: the paper's streams are an instance (all prefixes have length 2^pN and all suffixes mL; the separation is §8.7)
--   - reading: Bob continues the algorithm and recovers z_q with the same constant success probability → the protocol's message set is the configuration set S and its seed is the algorithm's seed; success in the inner-measure form; reason: this is the simulation the paragraph describes
--   - encoding: the algorithm's vectors, seed space and configurations → E, Ω and S in Lean's base universe Type; reason: Lean universe convention; the paper's instance (E = ℝ^d, finite S) lives in Type
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Proof of Theorem 8.1, p.36 (pdf_page 37)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_StreamAlg
import Definitions.Def_CosDensity_OneWayProtocol

open MeasureTheory

namespace CosDensity

/-- **Proof of Theorem 8.1: the reduction from INDEX.** Q. Zhang, *Frequency Moments Beyond
Equality: Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…),
Proof of Theorem 8.1, p.36 (pdf_page 37): "Alice runs the streaming algorithm on her prefix
vectors determined by input z and sends its memory configuration to Bob. Bob continues the
algorithm on the suffix vector set determined by input q and uses the algorithm's estimate of
M_p(P(z, q)) to recover z_q with the same constant success probability."

Let `pre z` (Alice's prefix, for `z ∈ {0,1}^N`) and `suf q` (Bob's suffix, for `q ∈ [N]`) be
streams whose lengths do not depend on `z` and on `q`, and suppose thresholds `θ_q` separate the
two cases: every `(1+ε)`-approximation `Y` of `M_p(pre z ++ suf q)` exceeds `θ_q` exactly when
`z_q = 1`. Then every randomized one-pass streaming algorithm with memory configurations `S` that
`(1+ε)`-approximates `M_p` with probability at least 2/3 on every stream `pre z ++ suf q` yields a
public-coin one-way protocol for INDEX_N, with message set `S` and the same seed, that errs with
probability at most 1/3.

**Formalization Note.** The two length conditions let Alice and Bob agree on the stream length
and on the position where Bob continues, which the model allows the algorithm to use. -/
theorem theorem_8_1_reduction {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} (p : ℕ) (ε : ℝ) (pre : (Fin N → Bool) → List E) (suf : Fin N → List E)
    (n₁ n₂ : ℕ) (hpre : ∀ z, (pre z).length = n₁) (hsuf : ∀ q, (suf q).length = n₂)
    (θ : Fin N → ℝ)
    (hsep : ∀ (z : Fin N → Bool) (q : Fin N) (Y : ℝ),
      IsApprox ε (moment p (pre z ++ suf q)) Y → (z q = true ↔ θ q < Y))
    (Ω S : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : StreamAlg E Ω S)
    (hA : ∀ (z : Fin N → Bool) (q : Fin N),
      SucceedsWP μ (fun ω => IsApprox ε (moment p (pre z ++ suf q))
        (A.estimate ω (pre z ++ suf q))) (2 / 3)) :
    ∃ π : OneWayProtocol N Ω S, SolvesIndex μ π := by sorry

end CosDensity
