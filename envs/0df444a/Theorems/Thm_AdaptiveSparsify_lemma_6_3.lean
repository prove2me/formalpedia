-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_6_3
-- name    : AdaptiveSparsify.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:36.587067+00:00
-- url     : https://prove2.me/theorems/2f603ff2-dcdd-4032-b635-8b1ec539df0d
-- title:
--   Lemma 6.3 — sampling by block norm, uniform weight and leverage overestimates gives a valid $R$
-- statement:
--   Let $D$ be block diagonal, let $A\in\mathbb R^{n\times d}$ with $DA$ of full column rank, let $\delta\in\mathbb R^n$, and let $\tilde\tau_i\ge\sum_{j\in S_i}\tau(DA)_j$, where $\tau(DA)_j$ is the leverage score of row $j$ of $DA$. Put $\Sigma_\tau=\sum_i\tilde\tau_i$ and $K=2\sqrt m+\Sigma_\tau$, and sample a block $i$ with probability
--
--   $$p_i=\frac{\sqrt m\big(\|\delta_i\|_2^2/\|\delta\|_2^2+1/m\big)+\tilde\tau_i}{K}.$$
--
--   For every $C_{\mathrm{var}}>0$ and failure exponent $c>0$ there is $C_0$ such that for $C\ge C_0$, $0<\alpha\le1$ and $n\ge2$, the matrix $R=\sum_{j=1}^{K'}(p_{i_j}K')^{-1}I_{S_{i_j}}$ built from $K'=\lceil C\alpha^{-2}\log n\cdot K\rceil$ independent samples is a valid sample in the sense of Definition 4.6, for $\delta$ and $DA$, with failure at most $n^{-c}$ in items 5 and 6.
--
--   This is how Algorithm 1 obtains its subsampling matrix: each step touches about $\sqrt m+d$ blocks.
--
--   Differences from the source:
--   - reading: the ratio ‖δ_i‖²/‖δ‖² at δ = 0 → 1/m; reason: 0/0 occurs at the exactly central feasible start (p.44); with 1/m, p stays a probability vector
--   - reading: K′ = Cα⁻² log n · K samples → K′ = ⌈Cα⁻² log n · K⌉; reason: the printed count need not be an integer
--   - reading: leverage scores τ(DA)_j of an unrestricted matrix → DA has full column rank; reason: leverage is defined here through the inverse of (DA)⊤DA; Algorithm 1 uses a full-rank matrix
--   - reading: α and n unrestricted → 0 < α ≤ 1, n ≥ 2; reason: as in §4, where log n > 0 and α is small
--   - reading: "with high probability" in items 5 and 6 of Definition 4.6 → failure at most n^{−c}, for every c and C_var, with C chosen after them; reason: p.44 uses "Pr ≤ n^{−c} for a large constant c"
--   - encoding: a random diagonal matrix R → weights on the finite sample space Fin K′ → Fin m and the diagonal of R as a function of the sample; reason: this is the law of the K′ independent draws
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma 6.3, p.42

import Mathlib
import Definitions.Def_AdaptiveSparsify_IPM

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 6.3**, p.42.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma 6.3, p.42.

"Consider a block-diagonal matrix D ∈ R^{n×n}, A ∈ R^{n×d}, and δ ∈ R^n. For i ∈ [m] corresponding to
block S_i ⊆ [n] let τ̃_i ≥ ∑_{j∈S_i} τ(DA)_j and Σ_τ = ∑_{i∈[m]} τ̃_i. Let K = 2√m + Σ_τ. Sample a
single i ∈ [m] with probability p_i := (√m(‖δ_i‖²₂/‖δ‖²₂ + 1/m) + τ̃_i)/K. For a sufficiently large
constant C take K′ = Cα⁻² log n · K samples i_1, …, i_{K′}, and let R = ∑_{j=1}^{K′} 1/(p_{i_j} K′) I_{S_{i_j}},
where I_{S_i} is the identity matrix on block i. Then R is valid according to Definition 4.6."

**Formalization Note.** `DA` has full column rank, without which the leverage scores `τ(DA)_j` are not
defined by the inverse. The ratio at `δ = 0` is `1/m`, `K′` is rounded up, and `0 < α ≤ 1` (as in §4).
Validity holds for every `C_var` and every failure exponent `c`, with `C` chosen after them. -/
theorem lemma_6_3 : ∀ Cvar c : ℝ, 0 < Cvar → 0 < c → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
    ∀ (B₀ : Blocks) (d : ℕ) (Db : ∀ i, Matrix (Fin (B₀.dim i)) (Fin (B₀.dim i)) ℝ)
      (A : Matrix (Fin B₀.n) (Fin d) ℝ) (δ : Fin B₀.n → ℝ) (τ : Fin B₀.m → ℝ) (α : ℝ),
      2 ≤ B₀.n → 0 < α → α ≤ 1 →
      ((B₀.assemble Db * A)ᵀ * (B₀.assemble Db * A)).PosDef →
      (∀ i, ∑ l, leverage ((B₀.assemble Db * A)ᵀ * (B₀.assemble Db * A))
        ((B₀.assemble Db * A) (B₀.coord i l)) ≤ τ i) →
      IsValidSample B₀
        (sampleWeight (K' := B₀.sampleCount C α τ) (B₀.sampleP δ τ))
        (fun idx => B₀.sampleR (B₀.sampleP δ τ) idx)
        δ (B₀.assemble Db * A) α Cvar ((B₀.n : ℝ) ^ (-c)) := by sorry

end AdaptiveSparsify
