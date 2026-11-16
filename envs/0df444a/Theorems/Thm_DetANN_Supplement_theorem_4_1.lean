-- Prove2me | Theorems.Thm_DetANN_Supplement_theorem_4_1
-- name    : DetANN.Supplement.theorem_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T04:18:48.34657+00:00
-- url     : https://prove2.me/theorems/705f428f-c5a7-4ff9-b470-ff4a46eabe0c
-- title:
--   Theorem 4.1, pp.8–9 — over all tuples $\omega\in[d]^s$ some answer is within factor $C_{\alpha,\tau,s}$ of the nearest distance, and $C_{\alpha,\tau,s}=\alpha+O(s^{-1/2}+\sqrt\tau)$
-- statement:
--   Let $d\ge1$, let $P\subseteq\mathbb R^d$ be finite, and let $A_1,\dots,A_d:\mathbb R^d\to\mathbb R^b$ be a $\tau$-balanced block system for $P$ (Definition 3.1) with $0<\tau<1$. Let $s\ge2$. For an ordered tuple $\omega=(i_1,\dots,i_s)\in[d]^s$ (repeated indices allowed) the **superblock** is
--   $$A_\omega z=A_{i_1}z\oplus\cdots\oplus A_{i_s}z\in\mathbb R^{sb},\qquad \|A_\omega z\|_2^2=\sum_{j=1}^s\|A_{i_j}z\|_2^2 .$$
--
--   Fix a query $q\in\mathbb R^d$ and a factor $\alpha\ge1$, and suppose that for every $\omega\in[d]^s$ a point $x_\omega\in P$ satisfies the local guarantee (11),
--   $$\|A_\omega(q-x_\omega)\|_2\le\alpha\min_{x\in P}\|A_\omega(q-x)\|_2 .$$
--
--   **Theorem.**
--
--   1. Then
--   $$\min_{\omega\in[d]^s}\|q-x_\omega\|_2\le C_{\alpha,\tau,s}\,\min_{x\in P}\|q-x\|_2,\qquad C_{\alpha,\tau,s}=\frac{\alpha+\sqrt{2\alpha^2/(s-1)+12\tau(1+\alpha)^2}}{\sqrt{1-\tau}} .$$
--   2. In particular, if $\alpha$ is bounded and $\tau\le1/2$, then $C_{\alpha,\tau,s}=\alpha+O(s^{-1/2}+\sqrt\tau)$: for every bound $A$ there is a constant $K$ such that $|C_{\alpha,\tau,s}-\alpha|\le K\,(s^{-1/2}+\sqrt\tau)$ for all $\alpha\in[1,A]$, $\tau\in(0,1/2]$ and integers $s\ge2$.
--
--   This is the correctness guarantee of the exhaustive construction of §4: querying one low-dimensional structure per superblock and returning the best candidate in the original space gives approximation factor $C_{\alpha,\tau,s}$, which is $1+\varepsilon$ for the parameters (12).
--
--   **Formalization Note** The exhaustive family is the published tuple-family framework (`DetANN.TupleFamily`) with tuples $\omega:\mathrm{Fin}\,s\to\mathrm{Fin}\,d$ and $S(\omega,j)=\omega_j$; the local guarantee is stated squared, which is equivalent for $\alpha\ge0$. The answers $x_\omega$ may depend on $q$.
--
--   Differences from the source:
--   - generalization: standing assumptions of §3 ($d$ a power of two, $P$ of size $n\ge d$) → any $d\ge1$ and any finite $P$; reason: Theorem 4.1 and its proof (§5) use only Definition 3.1 and averages over $[d]^s$; the paper's case is the special case.
--   - encoding: $\min_\omega\|q-x_\omega\|\le C\min_{x\in P}\|q-x\|$ → some $\omega$ has $\|q-x_\omega\|\le C\|q-y\|$ for every $y\in P$; reason: both minima are over finite nonempty sets ($d\ge1$, and $P$ contains the $x_\omega$).
--   - encoding: (11) $\|A_\omega(q-x_\omega)\|\le\alpha\min_{x\in P}\|A_\omega(q-x)\|$ → $\|A_\omega(q-x_\omega)\|^2\le\alpha^2\|A_\omega(q-y)\|^2$ for all $y\in P$; reason: both sides nonnegative and $\alpha\ge1$.
--   - reading: "if $\alpha$ is bounded and $\tau\le1/2$, then $C_{\alpha,\tau,s}=\alpha+O(s^{-1/2}+\sqrt\tau)$" → for every bound $A$ there is $K$ with $|C_{\alpha,\tau,s}-\alpha|\le K(s^{-1/2}+\sqrt\tau)$ for all $\alpha\in[1,A]$, $\tau\in(0,1/2]$, $s\ge2$; reason: standard meaning of the $O$-statement, with the constant depending only on the bound on $\alpha$; the two-sided form is the stronger reading.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Theorem 4.1, pp.8–9 (PDF pp.8–9); superblocks and (11), §4.1, p.8; Definition 3.1, p.7; proof in §5, pp.9–13

import Mathlib
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_TupleFamily

namespace DetANN

namespace Supplement

/-- **Theorem 4.1** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High
Dimensions*, STOC 2027 submission (manuscript sha256 96f0ad57…), pp.8–9).
Let `A₁, …, A_d` be a `τ`-balanced block system for `P`, with `0 < τ < 1`, and let `s ≥ 2`. Suppose
that for every `ω ∈ [d]^s` a point `x_ω ∈ P` satisfies (11) with factor `α ≥ 1`. Then for every
query `q`, `min_ω ‖q − x_ω‖ ≤ C_{α,τ,s} · min_{x ∈ P} ‖q − x‖`, where
`C_{α,τ,s} = (α + √(2α²/(s − 1) + 12τ(1 + α)²))/√(1 − τ)`. In particular, if `α` is bounded and
`τ ≤ 1/2`, then `C_{α,τ,s} = α + O(s^{−1/2} + √τ)`.

**Formalization Note.**
* The exhaustive family of §4.1 is `S ω j = ω j` over all ordered tuples `ω : Fin s → Fin d`
  (repetitions allowed), so `superNormSq A S ω z = ∑ⱼ ‖A_{ω j} z‖² = ‖A_ω z‖²`, blocks retained with
  multiplicity. The local guarantee (11) is `DetANN.LocalGuarantee`, its squared form, equivalent for
  `α ≥ 0`. The answers `x` are chosen after the query `q`, as in the paper.
* `min_ω ‖q − x_ω‖ ≤ C · min_{x∈P} ‖q − x‖` is written as: some `ω` has `‖q − x_ω‖ ≤ C‖q − y‖` for
  every `y ∈ P` (both minima are over finite nonempty sets).
* `d ≥ 1` is the paper's standing assumption and is needed: for `d = 0` there is no tuple `ω`. The
  other standing assumptions (`d` a power of two, `n ≥ d`) are not used by Theorem 4.1 and are
  dropped; `P` is any finite set (nonempty because it contains the `x_ω`).
* "In particular": for every bound `A` there is `K` such that `|C_{α,τ,s} − α| ≤ K(s^{−1/2} + √τ)`
  for all `α ∈ [1, A]`, `τ ∈ (0, 1/2]` and integers `s ≥ 2`; `s^{−1/2}` is `1/√s`. -/
theorem theorem_4_1 :
    (∀ {d b s : ℕ}, 1 ≤ d → 2 ≤ s →
      ∀ τ α : ℝ, 0 < τ → τ < 1 → 1 ≤ α →
        ∀ (P : Finset (EuclideanSpace ℝ (Fin d)))
          (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b)),
          IsBalancedBlockSystem τ P A →
          ∀ (q : EuclideanSpace ℝ (Fin d)) (x : (Fin s → Fin d) → EuclideanSpace ℝ (Fin d)),
            (∀ ω, x ω ∈ P) →
            LocalGuarantee A (fun (ω : Fin s → Fin d) (j : Fin s) => ω j) P q x α →
            ∃ ω : Fin s → Fin d, ∀ y ∈ P,
              ‖q - x ω‖ ≤
                (α + Real.sqrt (2 * α ^ 2 / ((s : ℝ) - 1) + 12 * τ * (1 + α) ^ 2)) /
                  Real.sqrt (1 - τ) * ‖q - y‖) ∧
    (∀ Abd : ℝ, ∃ K : ℝ, ∀ α τ : ℝ, 1 ≤ α → α ≤ Abd → 0 < τ → τ ≤ 1 / 2 →
      ∀ s : ℕ, 2 ≤ s →
        |(α + Real.sqrt (2 * α ^ 2 / ((s : ℝ) - 1) + 12 * τ * (1 + α) ^ 2)) /
            Real.sqrt (1 - τ) - α| ≤
          K * (1 / Real.sqrt s + Real.sqrt τ)) := by sorry

end Supplement

end DetANN
