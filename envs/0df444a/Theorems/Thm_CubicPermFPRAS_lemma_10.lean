-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_10
-- name    : CubicPermFPRAS.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:51.097145+00:00
-- url     : https://prove2.me/theorems/d9f3699c-32ac-423e-b063-1b594ef93873
-- title:
--   Lemma 10, p.13 — the activity schedule $1/n=a_0<\dots<a_m=J$: 3-warm stages, $\nu_J(\mathcal P)\ge1/2$, $\sum_k(1+\sqrt{a_k})=O(n)$
-- statement:
--   Fix $\alpha>1$ and $J_\alpha\ge8\alpha^2$. There is $K_0$ such that for every $K\ge K_0$ there is $C$ with the following property. For every $n\ge1$, positive activities $\lambda$, anchor $r$ and $\alpha$-rough anchor weights, the activity schedule $a_0<\dots<a_m$ built with constant $K$ and $J=J_\alpha n^2$ satisfies
--
--   1. $1/n=a_0<a_1<\dots<a_m=J$;
--   2. the point mass at $\sigma^*$ is 3-warm for $\nu_{a_0}$, and $\nu_{a_{k-1}}$ is 3-warm for $\nu_{a_k}$ for every $1\le k\le m$;
--   3. $\nu_J(\mathcal P)\ge1/2$;
--   4. $m+1\le Cn$ and $\sum_{k=0}^m(1+\sqrt{a_k})\le Cn$;
--   5. the construction uses at most $Cn^2$ operations (its tests plus the $m+1$ activities written).
--
--   This is the schedule along which the sampler raises the assignment activity from $1/n$ to $J$.
--
--   Differences from the source:
--   - generalization: the constant $K=\max\{A_\alpha,J_\alpha\}$ and "a deterministic algorithm constructs a schedule" → every $K\ge K_0$ (constants depending on $K$), for the proof's explicit schedule and construction; reason: the paper's $K$ is one admissible value, and the explicit construction witnesses the existential
--   - encoding: "in $O(n^2)$ time" → tests $+\,(m+1)\le Cn^2$; reason: the construction's operations are its inequality tests and the activities it writes
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 10, p.13 (PDF 15); construction and proof, pp.43–45 (PDF 45–47)

import Mathlib
import Definitions.Def_CubicPermFPRAS_nuAux
import Definitions.Def_CubicPermFPRAS_activitySchedule

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 10** (activity schedule), p.13 (PDF 15), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…); construction and proof on
pp.43–45 (PDF 45–47).

A deterministic algorithm constructs, in `O(n²)` time, a schedule `1/n = a₀ < a₁ < ⋯ < a_m = J`
such that the point mass at `σ*` is 3-warm for `ν_{a₀}` and `ν_{a_{k−1}}` is 3-warm for `ν_{a_k}`
for every `1 ≤ k ≤ m`. Moreover, `ν_J(P) ≥ 1/2`, the number of stages is `m + 1 = O(n)`, and
`∑_{k=0}^m (1 + √a_k) = O(n)` (13).

**Formalization Note.** The schedule is the one of the proof (step 2, p.44):
`a_{k+1} = min{J, (1 + 1/q(a_k)) a_k}` with `q(a)` the least power of two with
`q(a)² ≥ 16K(1 + min{n, n/√a})`; the time of the construction is its number of tests plus the
`m + 1` activities written (step 4, p.44–45). The paper takes `K = max{A_α, J_α}`; the statement
holds for every `K` beyond a threshold `K₀`, with constants depending on `K`. The §8.1 standing
assumptions (p.37) are the binders. -/
theorem lemma_10 : ∀ α : ℝ, 1 < α → ∀ Jα : ℝ, 8 * α ^ 2 ≤ Jα → ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (lam : Matrix (Fin n) (Fin n) ℝ), (∀ u v, 0 < lam u v) →
    ∀ (r : Fin n) (w : Fin n → ℝ), IsRoughAnchor α lam r w →
      actSeq K (Jα * (n : ℝ) ^ 2) n 0 = 1 / (n : ℝ) ∧
      (∀ k < actLen K (Jα * (n : ℝ) ^ 2) n,
        actSeq K (Jα * (n : ℝ) ^ 2) n k < actSeq K (Jα * (n : ℝ) ^ 2) n (k + 1)) ∧
      actSeq K (Jα * (n : ℝ) ^ 2) n (actLen K (Jα * (n : ℝ) ^ 2) n) = Jα * (n : ℝ) ^ 2 ∧
      1 / nuAux (Bmat lam w) (Jα * (n : ℝ) ^ 2) (actSeq K (Jα * (n : ℝ) ^ 2) n 0) (sigmaStar n) ≤ 3 ∧
      (∀ k, 1 ≤ k → k ≤ actLen K (Jα * (n : ℝ) ^ 2) n →
        ∑ σ, nuAux (Bmat lam w) (Jα * (n : ℝ) ^ 2) (actSeq K (Jα * (n : ℝ) ^ 2) n (k - 1)) σ ^ 2 /
          nuAux (Bmat lam w) (Jα * (n : ℝ) ^ 2) (actSeq K (Jα * (n : ℝ) ^ 2) n k) σ ≤ 3) ∧
      1 / 2 ≤ ∑ σ ∈ PSet n, nuAux (Bmat lam w) (Jα * (n : ℝ) ^ 2) (Jα * (n : ℝ) ^ 2) σ ∧
      ((actLen K (Jα * (n : ℝ) ^ 2) n : ℝ) + 1 ≤ C * n) ∧
      ∑ k ∈ Finset.range (actLen K (Jα * (n : ℝ) ^ 2) n + 1),
          (1 + Real.sqrt (actSeq K (Jα * (n : ℝ) ^ 2) n k)) ≤ C * n ∧
      ((actTests K (Jα * (n : ℝ) ^ 2) n + actLen K (Jα * (n : ℝ) ^ 2) n + 1 : ℕ) : ℝ) ≤
        C * (n : ℝ) ^ 2 := by sorry

end CubicPermFPRAS
