-- Prove2me | Theorems.Thm_DetANN_balanced_signs_exist
-- name    : DetANN.balanced_signs_exist
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:28.262585+00:00
-- url     : https://prove2.me/theorems/591f5c09-b0da-4b8c-a548-f9ced4b1cd3a
-- title:
--   Proof of Theorem 3.2, p.16 — signs with $\Phi\le1/8$ exist, so the signed blocks are $\tau$-balanced with $b=L$
-- statement:
--   There is an absolute constant $C_0^*>0$ such that for every $C_0\ge C_0^*$ the following holds. Let $d\ge1$, let $h$ be a $d\times d$ matrix with entries in $\{-1,+1\}$ and $h^\top h=dI$, let $\tau\in(0,1)$, let $P\subseteq\mathbb R^d$ be finite, and let $\mathcal D$ be a finite set of $N\ge1$ nonzero vectors that contains $x-y$ or $y-x$ for every pair of distinct $x,y\in P$. With $p_0=\lceil\log_4(8Nd)\rceil$ and $L=\lceil C_0\tau^{-2}p_0\rceil$ there is a sign assignment such that
--
--   1. $\Phi\le1/8<1$;
--   2. $\big|d\|A_jv\|_2^2-\|v\|_2^2\big|<\tau\|v\|_2^2$ for every $v\in\mathcal D$ and $j\in[d]$;
--   3. the signed blocks $A_1,\dots,A_d:\mathbb R^d\to\mathbb R^L$ form a $\tau$-balanced block system for $P$ (Definition 3.1) with $b=L$.
--
--   This is the existence content of Theorem 3.2: balanced blocks of dimension $L=O(\tau^{-2}\log(Nd))$ exist for every point set.
--
--   **Formalization Note** The operation counts of Theorem 3.2 are part of the resource bounds of Theorem 1.1, not of this statement.
--
--   Differences from the source:
--   - generalization: 𝒟 exactly one orientation of each nonzero difference of two points of P → any finite set of nonzero vectors containing such orientations, N = |𝒟| ≥ 1; reason: the set of oriented differences is such a set
--   - generalization: h the Walsh–Hadamard matrix, d a power of two, n ≥ d → any ±1 matrix with hᵀh = d·I, any d ≥ 1, any finite P; reason: the Walsh–Hadamard matrix is such a matrix
--   - reading: for a sufficiently large absolute constant C₀ → ∃ C₀* > 0 such that the conclusion holds for every C₀ ≥ C₀*; reason: the standard meaning
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Proof of Theorem 3.2, p.16 (PDF p.16); §6.3, p.15

import Mathlib
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_SignedBlocks

namespace DetANN

/-- **Proof of Theorem 3.2, the balanced signs** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), p.16; §6.3, p.15).
Let `P ⊆ ℝ^d` be finite, `τ ∈ (0, 1)`, and let `𝒟` be a finite set of `N ≥ 1` nonzero vectors containing
one orientation of each nonzero difference of two points of `P`. With `p₀ = ⌈log₄(8Nd)⌉` and
`L = ⌈C₀ τ^{−2} p₀⌉` for a sufficiently large absolute constant `C₀`, there is a sign assignment with
`Φ ≤ 1/8 < 1`, hence `|d‖A_j v‖² − ‖v‖²| < τ‖v‖²` for every `v ∈ 𝒟` and every `j`, and the signed
Hadamard blocks form a `τ`-balanced block system for `P` with `b = L`.

**Formalization Note.** "Sufficiently large absolute constant `C₀`" is the threshold form `∃ C₀* > 0,
∀ C₀ ≥ C₀*`, uniform in `d, h, τ, P, 𝒟`. `h` is any `d × d` matrix with entries `±1` and `hᵀh = d·I`
(the paper: Walsh–Hadamard, `d` a power of two). `𝒟` may contain further nonzero vectors besides
the orientations of the differences. This is the existence content of Theorem 3.2; its clauses on
`poly(n, d, 1/τ)` arithmetic operations and `O(bd log n)` evaluation time are not stated here (the
resource bounds of `DetANN.theorem_1_1` account for them). -/
theorem balanced_signs_exist :
    ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ → ∀ d : ℕ, 1 ≤ d →
      ∀ h : Matrix (Fin d) (Fin d) ℝ, (∀ j r, h j r = 1 ∨ h j r = -1) →
        h.transpose * h = (d : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) →
        ∀ τ : ℝ, 0 < τ → τ < 1 →
          ∀ P D : Finset (EuclideanSpace ℝ (Fin d)), (∀ v ∈ D, v ≠ 0) →
            (∀ x ∈ P, ∀ y ∈ P, x ≠ y → x - y ∈ D ∨ y - x ∈ D) → 1 ≤ D.card →
            ∃ ξ : Fin (numReps C₀ τ (momentOrder D.card d)) → Fin d → Bool,
              potential h (numReps C₀ τ (momentOrder D.card d)) ξ τ (momentOrder D.card d) D
                  ≤ 1 / 8 ∧
                (∀ v ∈ D, ∀ j : Fin d,
                  |(d : ℝ) * ‖signedBlocks h (numReps C₀ τ (momentOrder D.card d)) ξ j v‖ ^ 2
                      - ‖v‖ ^ 2| < τ * ‖v‖ ^ 2) ∧
                IsBalancedBlockSystem τ P (signedBlocks h (numReps C₀ τ (momentOrder D.card d)) ξ)
                  := by sorry

end DetANN
